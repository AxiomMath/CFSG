module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGOrdPToralMax (U : Type*) [Group U] (p : ℕ) : Prop :=
  ∀ u : U, u ^ p = 1 → ∃ E : Subgroup U, IsElemAbelian p E ∧ u ∈ E ∧
    ∀ A : Subgroup U, IsElemAbelian p A → Nat.card A ≤ Nat.card E

namespace OrdPInnerExc

section Basic

variable {X Y : Type*} [Group X] [Group Y] {p : ℕ}

theorem isElemAbelian_map (φ : X →* Y) {E : Subgroup X} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_zpowers {x : X} (hx : x ^ p = 1) : IsElemAbelian p (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

theorem commute_of_isElemAbelian {E : Subgroup X} (hE : IsElemAbelian p E) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

end Basic

section Kernel

variable {U G : Type*} [Group U] [Group G] {ψ : U →* G} {p : ℕ}

theorem eq_one_of_mem_ker (hcop : Nat.Coprime (Nat.card ψ.ker) p) {z : U} (hz : z ∈ ψ.ker)
    (hzp : z ^ p = 1) : z = 1 := by
  have hk : z ^ Nat.card ψ.ker = 1 := by
    have h := pow_card_eq_one' (G := ψ.ker) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val h
  have h := pow_gcd_eq_one.mpr ⟨hk, hzp⟩
  rwa [hcop, pow_one] at h

theorem exists_preimage_pow_eq_one (hp : p.Prime) (hcop : Nat.Coprime (Nat.card ψ.ker) p)
    {y : G} (hy : y ∈ ψ.range) (hyp : y ^ p = 1) : ∃ u : U, ψ u = y ∧ u ^ p = 1 := by
  obtain ⟨u₀, rfl⟩ := hy
  set k := Nat.card ψ.ker with hk
  have hmem : u₀ ^ p ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hyp]
  have hpk : (u₀ ^ p) ^ k = 1 := congrArg Subtype.val (pow_card_eq_one' (G := ψ.ker)
    (x := ⟨u₀ ^ p, hmem⟩))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨u₀ ^ (k * m), ?_, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hyp, hm, pow_one]
  · rw [← pow_mul, show k * m * p = p * k * m by ring, pow_mul, pow_mul, hpk, one_pow]

theorem pow_conj_eq_of_central {x y c : U} (hc : c ∈ Subgroup.center U)
    (h : x * y * x⁻¹ = c * y) (n : ℕ) : x ^ n * y * (x ^ n)⁻¹ = c ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcx : x * c ^ n = c ^ n * x := Subgroup.mem_center_iff.mp
      (Subgroup.pow_mem _ hc n) x
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * c ^ n * y * x⁻¹ := by rw [ih]; group
      _ = c ^ n * (x * y * x⁻¹) := by rw [hcx]; group
      _ = c ^ (n + 1) * y := by rw [h, pow_succ]; group

theorem commute_of_lift (hkc : ψ.ker ≤ Subgroup.center U) (hcop : Nat.Coprime (Nat.card ψ.ker) p)
    {x y : U} (hxp : x ^ p = 1) (hxy : ψ x * ψ y = ψ y * ψ x) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcker : c ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
    group
  have hcent := hkc hcker
  have h1 : x * y * x⁻¹ = c * y := by rw [hc]; group
  have h2 := pow_conj_eq_of_central hcent h1 p
  rw [hxp, one_mul, inv_one, mul_one] at h2
  have hcp : c ^ p = 1 := by
    have h3 := congrArg (· * y⁻¹) h2
    simp only [mul_inv_cancel, mul_assoc] at h3
    rw [mul_one] at h3
    exact h3.symm
  have hc1 : c = 1 := eq_one_of_mem_ker hcop hcker hcp
  have : x * y * x⁻¹ * y⁻¹ = 1 := hc1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [this, one_mul]

variable [Finite G]

theorem exists_elemAbelian_lift_mem (hp : p.Prime) (hkc : ψ.ker ≤ Subgroup.center U)
    (hcop : Nat.Coprime (Nat.card ψ.ker) p) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hBr : B ≤ ψ.range) {u : U} (hu : u ^ p = 1) (huB : ψ u ∈ B) :
    ∃ A : Subgroup U, IsElemAbelian p A ∧ u ∈ A ∧ Nat.card B ≤ Nat.card A := by
  have hlift : ∀ b : B, ∃ u : U, ψ u = b ∧ u ^ p = 1 := fun b =>
    exists_preimage_pow_eq_one hp hcop (hBr b.2) (hB.2 b b.2)
  choose s hs hsp using hlift
  set S : Set U := insert u (Set.range s) with hS
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro x (rfl | ⟨a, rfl⟩)
    · exact hu
    · exact hsp a
  have hSB : ∀ x ∈ S, ψ x ∈ B := by
    rintro x (rfl | ⟨a, rfl⟩)
    · exact huB
    · rw [hs]; exact a.2
  set A := Subgroup.closure S with hA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    have hc := Subgroup.isMulCommutative_closure (k := S) fun x hx y hy _ =>
      commute_of_lift hkc hcop (hSp x hx) (commute_of_isElemAbelian hB (hSB x hx) (hSB y hy))
    exact fun x hx y hy => congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : ∀ x ∈ A, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hSp x hx
    | one => exact one_pow p
    | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hcomm x hx y hy) p), ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hAel : IsElemAbelian p A :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hAp⟩
  have hinj : Function.Injective fun a : A => ψ a := by
    intro a b hab
    have hmem : (b : U)⁻¹ * a ∈ ψ.ker := by
      have hab' : ψ a = ψ b := hab
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    have h1 := eq_one_of_mem_ker hcop hmem (hAp _ (A.mul_mem (A.inv_mem b.2) a.2))
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have : Finite A := Finite.of_injective _ hinj
  refine ⟨A, hAel, Subgroup.subset_closure (Set.mem_insert u _),
    Nat.card_le_card_of_injective (fun b => (⟨s b, Subgroup.subset_closure
      (Set.mem_insert_of_mem u ⟨b, rfl⟩)⟩ : A)) fun a b hab => ?_⟩
  have h := congrArg (fun x : A => ψ x) hab
  simp only [hs] at h
  exact Subtype.ext h

theorem exists_elemAbelian_lift (hp : p.Prime) (hkc : ψ.ker ≤ Subgroup.center U)
    (hcop : Nat.Coprime (Nat.card ψ.ker) p) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hBr : B ≤ ψ.range) : ∃ A : Subgroup U, IsElemAbelian p A ∧ Nat.card B ≤ Nat.card A := by
  obtain ⟨A, hA, -, hc⟩ := exists_elemAbelian_lift_mem hp hkc hcop hB hBr (one_pow p)
    (by rw [map_one]; exact B.one_mem)
  exact ⟨A, hA, hc⟩

theorem card_le_card_map (hcop : Nat.Coprime (Nat.card ψ.ker) p) {E : Subgroup U}
    (hE : IsElemAbelian p E) : Nat.card E ≤ Nat.card (E.map ψ) := by
  refine Nat.card_le_card_of_injective (fun e : E => (⟨ψ e, e, e.2, rfl⟩ : E.map ψ))
    fun a b hab => ?_
  have h : ψ a = ψ b := congrArg Subtype.val hab
  have hmem : (b : U)⁻¹ * a ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h1 := eq_one_of_mem_ker hcop hmem (hE.2 _ (E.mul_mem (E.inv_mem b.2) a.2))
  exact Subtype.ext (inv_mul_eq_one.mp h1).symm

theorem ggOrdPToralMax_of_surjective (hp : p.Prime) (hψ : Function.Surjective ψ)
    (hkc : ψ.ker ≤ Subgroup.center U) (hcop : Nat.Coprime (Nat.card ψ.ker) p)
    (h : GGOrdPToralMax G p) : GGOrdPToralMax U p := by
  intro u hu
  obtain ⟨E, hEel, huE, hmax⟩ := h (ψ u) (by rw [← map_pow, hu, map_one])
  obtain ⟨A, hAel, huA, hEA⟩ := exists_elemAbelian_lift_mem hp hkc hcop hEel
    (fun x _ => MonoidHom.mem_range.mpr (hψ x)) hu huE
  exact ⟨A, hAel, huA, fun A' hA' => ((card_le_card_map hcop hA').trans
    (hmax _ (isElemAbelian_map ψ hA'))).trans hEA⟩

end Kernel

section Reduction

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

omit [Finite G] in
theorem mem_of_mul_mem_centralizer (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) {c g : G}
    (hg : g ∈ G₀) (hcg : c * g ∈ Subgroup.centralizer (G₀ : Set G)) : c ∈ G₀ := by
  rw [hC, Subgroup.mem_bot, mul_eq_one_iff_eq_inv] at hcg
  rw [hcg]
  exact G₀.inv_mem hg

theorem exists_elemAbelian_four (hS : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
    (h4 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)))
    (hkc : ψ.ker ≤ Subgroup.center U) (hcop : Nat.Coprime (Nat.card ψ.ker) p) (hBs : Bs ≤ G₀) :
    ∃ A : Subgroup U, IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A := by
  rw [← hS.range_eq] at hBs
  obtain ⟨A, hAel, hAc⟩ := exists_elemAbelian_lift hS.prime hkc hcop hS.2.2.2.1.2.1 hBs
  exact ⟨A, hAel, (hS.pow_four_le h4).trans hAc⟩

theorem exists_conj_of_toralMax (hS : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
    (hkc : ψ.ker ≤ Subgroup.center U) (hcop : Nat.Coprime (Nat.card ψ.ker) p) (hBs : Bs ≤ G₀)
    (hT : GGOrdPToralMax U p) {y : G} (hy : y ∈ G₀) (hyp : y ^ p = 1) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have hrange := hS.range_eq
  rw [← hrange] at hy hBs
  obtain ⟨u, rfl, hup⟩ := exists_preimage_pow_eq_one hS.prime hcop hy hyp
  obtain ⟨E, hEel, huE, hmax⟩ := hT u hup
  obtain ⟨A, hAel, hAc⟩ := exists_elemAbelian_lift hS.prime hkc hcop hS.2.2.2.1.2.1 hBs
  have hEM : E.map ψ ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨e, -, rfl⟩
    exact Subgroup.le_normalizer (hrange ▸ ⟨e, rfl⟩)
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS hEM (isElemAbelian_map ψ hEel)
    ((hAc.trans (hmax A hAel)).trans (card_le_card_map hcop hEel)) ?_
  rintro _ ⟨e, he, rfl⟩
  rw [← map_mul, ← map_mul, commute_of_isElemAbelian hEel huE he]

end Reduction

section Toral

variable {p : ℕ}

theorem ggOrdPToralMax_of_conj_le {C : Type} [Group C] [Finite C] {V : Subgroup C}
    (hV : IsElemAbelian p V)
    (hconj : ∀ A : Subgroup C, IsElemAbelian p A →
      ∃ g : C, A.map (MulAut.conj g).toMonoidHom ≤ V) :
    GGOrdPToralMax C p := by
  intro u hu
  obtain ⟨g, hg⟩ := hconj _ (isElemAbelian_zpowers hu)
  have hgu : g * u * g⁻¹ ∈ V := hg ⟨u, Subgroup.mem_zpowers u, rfl⟩
  refine ⟨V.map (MulAut.conj g⁻¹).toMonoidHom, isElemAbelian_map _ hV, ⟨_, hgu, ?_⟩, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · intro A hA
    obtain ⟨g', hg'⟩ := hconj A hA
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      ← Subgroup.card_map_of_injective (f := (MulAut.conj g').toMonoidHom)
        (MulAut.conj g').injective]
    exact Subgroup.card_le_of_le hg'

theorem ggOrdPToralMax_of_mulEquiv {U C : Type} [Group U] [Group C] (e : U ≃* C)
    (h : GGOrdPToralMax C p) : GGOrdPToralMax U p := by
  intro u hu
  obtain ⟨E, hEel, huE, hmax⟩ := h (e u) (by rw [← map_pow, hu, map_one])
  refine ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hEel, ⟨e u, huE, by simp⟩, ?_⟩
  intro A hA
  rw [Subgroup.card_map_of_injective e.symm.injective,
    ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact hmax _ (isElemAbelian_map _ hA)

end Toral

end OrdPInnerExc

end CFSG.StandardType
