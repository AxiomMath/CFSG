module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3Ratio
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3Type3
import CFSG.RankThree.PartTwo.Sec4.Ronan430L3ThetaSL
import CFSG.RankThree.PartTwo.Sec4.Wales430Heis
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofEven
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {H : Type} [Group H] [Finite H] {L : Subgroup H} [hLn : L.Normal]
  {p f : ℕ} {π : Bool}

theorem false_of_slPi_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A) {a : H}
    (ha3 : orderOf a = 3) (hAa : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers a)
    (hpgl : ∀ x ∈ A, ∃ y, IsPGLAt e x y) {a' u v : H} (ha'A : a' ∈ A)
    (huC : u ∈ Subgroup.centralizer (L : Set H)) (hvL : v ∈ L)
    (hvC : v ∉ Subgroup.centralizer (L : Set H)) (hv3 : orderOf v = 3)
    (hALC : A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) = Subgroup.closure {a, u * v})
    (hcomm : u * a' * u⁻¹ * a'⁻¹ = a) {c : H} (hcA : c ∈ A) (hca : c ∉ Subgroup.zpowers a)
    (hWc : Subgroup.normalizer (A : Set H) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set H))
    {R : Subgroup H} (hRL : R ≤ L) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set H)) (hRc : ⁅R, Subgroup.zpowers c⁆ = R)
    (hR1 : R ≠ ⊥) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hcomm' : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨haL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA ha3 hAa
  have haA : a ∈ A := (hAa ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have haC : a ∈ Subgroup.centralizer (L : Set H) :=
    (hAa ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).2
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha3
    omega
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have huvA : u * v ∈ A := by
    have : u * v ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) := by
      rw [hALC]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact this.1
  have hua : u * a = a * u := (Subgroup.mem_centralizer_iff.mp huC a haL).symm
  have huv : u * v = v * u := (Subgroup.mem_centralizer_iff.mp huC v hvL).symm
  have ha'uv : a' * (u * v) = (u * v) * a' := hcomm' a' ha'A _ huvA
  have ha'u : a' * u * a'⁻¹ = a⁻¹ * u := by
    have h1 : u * a' * u⁻¹ = a * a' := by rw [← hcomm]; group
    have h2 : a' * u⁻¹ * a'⁻¹ = u⁻¹ * a := by
      calc a' * u⁻¹ * a'⁻¹ = u⁻¹ * (u * a' * u⁻¹) * a'⁻¹ := by group
        _ = u⁻¹ * a := by rw [h1]; group
    calc a' * u * a'⁻¹ = (a' * u⁻¹ * a'⁻¹)⁻¹ := by group
      _ = a⁻¹ * u := by rw [h2]; group
  have ha'v : a' * v * a'⁻¹ = a * v := by
    have h1 : (a' * u * a'⁻¹) * (a' * v * a'⁻¹) = u * v := by
      calc (a' * u * a'⁻¹) * (a' * v * a'⁻¹) = a' * (u * v) * a'⁻¹ := by group
        _ = u * v := by rw [ha'uv, mul_inv_cancel_right]
    rw [ha'u] at h1
    calc a' * v * a'⁻¹ = u⁻¹ * a * (a⁻¹ * u * (a' * v * a'⁻¹)) := by group
      _ = u⁻¹ * a * (u * v) := by rw [h1]
      _ = a * v := by rw [show u⁻¹ * a * (u * v) = u⁻¹ * (a * u) * v by group, ← hua]; group
  have hea : ((e ⟨a, haL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    obtain ⟨l, hl⟩ := e.surjective ⟨x, hx⟩
    have hal : (⟨a, haL⟩ : L) * l = l * ⟨a, haL⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp haC l l.2).symm
    have := congrArg (fun z => ((e z : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hal
    simp only [map_mul, Subgroup.coe_mul] at this
    rw [hl] at this
    exact this
  obtain ⟨ζ, hζ⟩ := hea
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply ha1
    have : e ⟨a, haL⟩ = 1 := Subtype.ext (by rw [← hζ, map_one]; rfl)
    rw [map_eq_one_iff _ e.injective] at this
    exact congrArg Subtype.val this
  set V : GL (Fin 3) K := (e ⟨v, hvL⟩ : GL (Fin 3) K) with hV
  obtain ⟨y₁, hy₁⟩ := hpgl a' ha'A
  have hy₂ : IsPGLAt e (u * v) V := by
    have := isPGLAt_mul e (isPGLAt_of_mem_centralizer e huC) (isPGLAt_of_mem e hπ hvL)
    rwa [one_mul] at this
  have hav : a' * v * a'⁻¹ ∈ L := hLn.conj_mem v hvL a'
  have hheis : y₁ * V * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * V := by
    rw [hV, ← coe_e_conj_of_isPGLAt hy₁ hvL hav]
    have : (⟨a' * v * a'⁻¹, hav⟩ : L) = ⟨a, haL⟩ * ⟨v, hvL⟩ := Subtype.ext ha'v
    rw [this, map_mul, Subgroup.coe_mul, ← hζ]
  have htype : ∀ x ∈ A, x ∉ L ⊔ Subgroup.centralizer (L : Set H) → ∀ y, IsPGLAt e x y →
      Type123 π (p ^ f) K y 3 := by
    intro x hx hxLC y hy
    have hxC : x ∉ Subgroup.centralizer (L : Set H) := fun h => hxLC (Subgroup.mem_sup_right h)
    rcases type13_of_heis (hpgl := hpgl) hK hq hcomm' (mk_mem_range_pglHom (hA' := hpgl) ha'A hy₁)
        (mk_mem_range_pglHom (hA' := hpgl) huvA hy₂) hζ1 hheis hx hxC (hA3 x hx) hy with h1 | h3
    · exfalso
      obtain ⟨w, -, -, hw, -⟩ := exists_inner_decomp hK hq hy h1
      apply hxLC
      have : x = (x * (w : H)⁻¹) * w := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left w.2)
    · exact h3
  have hvx : ∀ x ∈ A, v * x * v⁻¹ * x⁻¹ ∈ Subgroup.zpowers a := by
    intro x hx
    obtain ⟨y, hy⟩ := hpgl x hx
    have hxv : x * v⁻¹ * x⁻¹ ∈ L := hLn.conj_mem _ (L.inv_mem hvL) x
    have hmL : v * (x * v⁻¹ * x⁻¹) ∈ L := L.mul_mem hvL hxv
    have hsc := isPGLAt_commutator_mem hK hq (hcomm' _ huvA x hx) hy₂ hy
    have hem : ((e ⟨v * (x * v⁻¹ * x⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        V * y * V⁻¹ * y⁻¹ := by
      have e1 : (⟨v * (x * v⁻¹ * x⁻¹), hmL⟩ : L) = ⟨v, hvL⟩ * ⟨x * v⁻¹ * x⁻¹, hxv⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAt hy (L.inv_mem hvL) hxv]
      have e2 : (⟨v⁻¹, L.inv_mem hvL⟩ : L) = (⟨v, hvL⟩ : L)⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv, hV]
      group
    have hmC := mem_centralizer_of_scalar hmL (by rw [hem]; exact hsc)
    have : v * x * v⁻¹ * x⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set H) :=
      ⟨by simpa [mul_assoc] using hmL, by simpa [mul_assoc] using hmC⟩
    rwa [hLC] at this
  have hvA : v ∈ Subgroup.normalizer (A : Set H) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have : v * x * v⁻¹ = (v * x * v⁻¹ * x⁻¹) * x := by group
    rw [this]
    exact A.mul_mem (Subgroup.zpowers_le.mpr haA (hvx x hx)) hx
  have hvc : v * c = c * v := by
    have hcc := (Subgroup.mem_normalizer_iff.mp (hWc hvA) c).mp (Subgroup.mem_zpowers c)
    have hm := hvx c hcA
    have hco : orderOf c = 3 := orderOf_eq_prime (hA3 c hcA) hc1
    have hm1 : v * c * v⁻¹ * c⁻¹ = 1 := by
      by_contra hne
      have hmc : v * c * v⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
        Subgroup.mul_mem _ hcc (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
      have hmo : orderOf (v * c * v⁻¹ * c⁻¹) = 3 :=
        orderOf_eq_prime (hA3 _ (Subgroup.zpowers_le.mpr haA hm)) hne
      have h1 : Subgroup.zpowers (v * c * v⁻¹ * c⁻¹) = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hm)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hmo, ha3])
      have h2 : Subgroup.zpowers (v * c * v⁻¹ * c⁻¹) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmc)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hmo, hco])
      exact hca (h1 ▸ h2 ▸ Subgroup.mem_zpowers c)
    calc v * c = v * c * v⁻¹ * c⁻¹ * c * v := by group
      _ = c * v := by rw [hm1, one_mul]
  have hcH : c ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) := by
    refine ⟨hcA, ?_⟩
    by_contra hcLC
    obtain ⟨yc, hyc⟩ := hpgl c hcA
    have h3 := htype c hcA hcLC yc hyc
    have hcomm'' : yc * V = V * yc := isPGLAt_commute_of_mem hvL hvc.symm hyc
    have hV3 : V ^ 3 = 1 := by
      rw [hV, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨v, hvL⟩ : L) ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← hv3, pow_orderOf_eq_one]; rfl)
      rw [this, map_one, Subgroup.coe_one]
    have hVZ : V ∉ StatedScalars (Fin 3) K := fun h => hvC (mem_centralizer_of_scalar hvL h)
    exact false_of_commute_type3_of_cube hτ hτ1 h3 hV3 hVZ hcomm''
  have ha'H : a' ∉ A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) := by
    rw [hALC]
    intro h
    have hle : Subgroup.closure {a, u * v} ≤ Subgroup.centralizer ({u} : Set H) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hua.symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rw [mul_assoc, ← huv, ← mul_assoc]
    have hu : a' * u = u * a' := Subgroup.mem_centralizer_singleton_iff.mp (hle h)
    apply ha1
    rw [← hcomm, ← hu]
    group
  refine false_of_gen hA.1 inf_le_left hcH hc1 ha'A ha'H (fun x hx hxH t htL ht2 hxt => ?_)
    hRL hR2 hAR hRc hR1
  have hxLC : x ∉ L ⊔ Subgroup.centralizer (L : Set H) := fun h => hxH ⟨hx, h⟩
  obtain ⟨y, hy⟩ := hpgl x hx
  exact eq_one_of_isPGLAt_type3 hK hy (htype x hx hxLC y hy) htL ht2 hxt

section Certs


theorem false_of_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hLp : Group.IsPerfect L)
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) {a : H} (ha3 : orderOf a = 3)
    (hAa : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers a)
    (hpgl : ∀ x ∈ A, ∃ y, IsPGLAt e x y)
    (hnofield : ∀ σ ∈ A, ¬ InducesStdKind L σ .field) {c : H} (hcA : c ∈ A)
    (hca : c ∉ Subgroup.zpowers a) {B : Subgroup H} (hsup : Subgroup.zpowers c ⊔ B = A)
    (hinf : Subgroup.zpowers c ⊓ B = ⊥)
    (hWc : Subgroup.normalizer (A : Set H) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set H))
    (hWB : Subgroup.normalizer (A : Set H) ≤ Subgroup.normalizer (B : Set H))
    {R : Subgroup H} (hRL : R ≤ L) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set H)) (hRc : ⁅R, Subgroup.zpowers c⁆ = R)
    (hR1 : R ≠ ⊥) : False := by
  classical
  have haA : a ∈ A := (hAa ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).1
  have haC : a ∈ Subgroup.centralizer (L : Set H) :=
    (hAa ▸ Subgroup.mem_zpowers a : a ∈ A ⊓ _).2
  have hAmax : ∀ x : H, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A := fun x hx3 hxA =>
    mem_of_maximal_of_commute hA hx3 fun y hy => (hxA y hy).symm
  rcases alt411_of_pgl hK hq e hA (by rw [hA27]) ha3 hAa hpgl with
    ⟨-, h9, -⟩ | ⟨-, hHeis⟩ |
      ⟨-, -, a', ha'A, -, u, v, huC, -, hvL, hvC, -, hv3, hALC, -, hcomm⟩ |
      ⟨-, σ, hσ, hσf, -⟩ | ⟨-, σ, hσ, hσf, -⟩ | ⟨-, σ, hσ, hσf, -⟩
  ·
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ A ⊓ L, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push Not at hcon
      have hle := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers a from hcon)
      rw [h9, Nat.card_zpowers, ha3] at hle
      omega
    obtain ⟨P, hPL, T, hTL, hPN, hTN, r, hr1, hrmul, hrker, hrP, hrT⟩ :=
      exists_theta_of_slPi hK hq e hA ha3 hAa hpgl (Subgroup.mem_inf.mp hb).1
        (Subgroup.mem_inf.mp hb).2 hba
    exact false_of_ratio hA.1 hA27 haA hcA hca hsup hinf (hWc hPN) (hWB hPN) (hWc hTN) (hWB hTN)
      (Subgroup.mem_centralizer_iff.mp haC T hTL) hr1 hrmul hrker hrP hrT
  ·
    exact Proof430.false_of_isHeisCentral hA.1 hA27 hAmax hLp haA hcA hAa ha3 hca hWc hHeis
  ·
    exact false_of_slPi_three hK hq e hA ha3 hAa hpgl ha'A huC hvL hvC hv3 hALC hcomm hcA hca
      hWc hRL hR2 hAR hRc hR1
  · exact hnofield σ hσ hσf
  · exact hnofield σ hσ hσf
  · exact hnofield σ hσ hσf

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
