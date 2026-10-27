module

public import CFSG.Quasithin.EmptyFaithful.S146zDBase
public import CFSG.CharacterTheory.Burnside

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section AutFix

variable {W : Type*} [Group W] [Finite W]

theorem card_mulAut_eight (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1)
    (h8 : Nat.card W = 8) : Nat.card (MulAut W) = 168 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq (n := 3)
    (by rw [h8]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_succ]

theorem card_stabilizer_mulAut (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1)
    (h8 : Nat.card W = 8) {w : W} (hw : w ≠ 1) :
    Nat.card (MulAction.stabilizer (MulAut W) w) = 24 := by
  classical
  have horb : MulAction.orbit (MulAut W) w = {x : W | x ≠ 1} := by
    ext x
    constructor
    · rintro ⟨φ, rfl⟩
      show φ w ≠ 1
      intro h
      apply hw
      have : φ w = φ 1 := by rw [h, map_one]
      exact φ.injective this
    · intro hx
      obtain ⟨σ, hσ⟩ := exists_mulAut_apply_eq hcomm hsq h8 hw hx
      exact ⟨σ, hσ⟩
  have h7 : (MulAction.orbit (MulAut W) w).ncard = 7 := by
    rw [horb]
    have hu : (Set.univ : Set W).ncard = 8 := by rw [Set.ncard_univ]; exact h8
    have hsplit : (Set.univ : Set W) = {1} ∪ {x : W | x ≠ 1} := by
      ext x; by_cases hx : x = 1 <;> simp [hx]
    have hdisj : Disjoint ({1} : Set W) {x : W | x ≠ 1} := by
      rw [Set.disjoint_left]; intro x hx hx'; exact hx' hx
    rw [hsplit, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton] at hu
    omega
  have hidx := MulAction.index_stabilizer (MulAut W) w
  have hm := Subgroup.index_mul_card (MulAction.stabilizer (MulAut W) w)
  rw [hidx, h7, card_mulAut_eight hcomm hsq h8] at hm
  omega

theorem perfect_aut_fix (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1)
    (h8 : Nat.card W = 8) {P : Subgroup (MulAut W)} (hP : ⁅P, P⁆ = P) {w : W} (hw : w ≠ 1)
    (hfix : ∀ φ ∈ P, φ w = w) : P = ⊥ := by
  classical
  have hPS : P ≤ MulAction.stabilizer (MulAut W) w := fun φ hφ => hfix φ hφ
  have hS : Group.IsSolvable (MulAction.stabilizer (MulAut W) w) := by
    have : Fintype (MulAction.stabilizer (MulAut W) w) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
      (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, card_stabilizer_mulAut hcomm hsq h8 hw]; norm_num)
  have hPsolv : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPS)
  by_contra hne
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have hperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  exact Group.IsPerfect.not_isSolvable ↥P hPsolv

end AutFix

end CFSG.Quasithin.ThreeD

namespace CFSG.Quasithin.ThreeC

section PerfFix

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem CCtx.perf_trivial (c : CCtx T M K U₁ U₂ s) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPZ : P ≤ Subgroup.normalizer (Zz : Set G)) (hPU : P ≤ Subgroup.normalizer (U₁ : Set G))
    {a : G} (ha : a ∈ U₁) (haZ : a ∉ Zz) (hfix : ∀ p ∈ P, p * a * p⁻¹ * a⁻¹ ∈ Zz) :
    ∀ p ∈ P, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz := by
  classical
  have hel := c.hSec.isElemAbelian_tilde
  have hcommW : ∀ x y : ↥(tildeOf Zz U₁), x * y = y * x := fun x y =>
    Subtype.ext (isElemAbelian_comm hel x.2 y.2)
  have hsqW : ∀ x : ↥(tildeOf Zz U₁), x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel x.2)
  have hUZ : U₁ ≤ Subgroup.normalizer (Zz : Set G) := c.hSec.norm
  set ψ := secRho hPZ hPU with hψ
  have hperfP : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hperfR : Group.IsPerfect ↥ψ.range := by
    have := hperfP
    exact Group.IsPerfect.range ψ
  have hperfR' : ⁅ψ.range, ψ.range⁆ = ψ.range := Subgroup.isPerfect_iff.mp hperfR
  have hne1 : tildeElt hUZ a ha ≠ 1 := by
    intro h
    apply haZ
    have h1 := congrArg
      (fun w : ↥(tildeOf Zz U₁) => (w : SecQuot (Subgroup.normalizer (Zz : Set G)) Zz)) h
    exact secMk_eq_one_iff.mp (by simpa [tildeElt] using h1)
  have hfix' : ∀ φ ∈ ψ.range, φ (tildeElt hUZ a ha) = tildeElt hUZ a ha := by
    rintro φ ⟨x, rfl⟩
    exact (secRho_apply_tildeElt_iff hPZ hPU hUZ x a ha).mpr (hfix x x.2)
  have hbot := ThreeD.perfect_aut_fix hcommW hsqW c.hSec.card_tilde hperfR' hne1 hfix'
  intro p hp w hw
  have h1 : ψ ⟨p, hp⟩ = 1 := by
    have : ψ ⟨p, hp⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact this
  exact commutator_mem_of_secRho_eq_one hPZ hPU hUZ (x := ⟨p, hp⟩) h1 hw

end PerfFix

section PerfUK

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem CCtx.exists_decomp_sup (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {w : G}
    (hw : w ∈ U₁ ⊔ U₂) : ∃ a ∈ U₁, ∃ b ∈ U₂, w = a * b := by
  have hcommU : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure hx hy
  have hN₁₂ : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy => hcommU x (c.hU₁U hx) y (c.hU₂U hy)
  have hw' : w ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN₁₂] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
  exact ⟨a, ha, b, hb, rfl⟩

theorem CCtx.perf_trivial_UK (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hPU : P ≤ Subgroup.normalizer (uOfL22 T M : Set G)) (hPZ : P ≤ Subgroup.normalizer (Zz : Set G))
    (hPU₁ : P ≤ Subgroup.normalizer (U₁ : Set G)) {a : G} (ha : a ∈ U₁ ⊔ U₂) (haZ : a ∉ Zz)
    (hfix : ∀ p ∈ P, p * a * p⁻¹ * a⁻¹ ∈ Zz) :
    ∀ p ∈ P, ∀ y ∈ U₁ ⊔ U₂, p * y * p⁻¹ * y⁻¹ ∈ Zz := by
  classical
  have hsZ := c.hsZ
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsH : s ∈ mcOf T := hG.1.1 c.hs
  have hcommU : ∀ x ∈ uOfL22 T M, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    S.comm_of_mem_conjClosure hx hy
  have hP₂ : ∀ p ∈ P, conjSub p U₂ = U₂ := fun p hp =>
    c.conjSub_U₂ S (hPK hp) (hPU hp) (hPZ hp) (conjSub_eq_of_mem_normalizer (hPU₁ hp))
  have hP₂' : ∀ p ∈ P, p ∈ Subgroup.normalizer (U₂ : Set G) := fun p hp =>
    mem_normalizer_of_conjSub_eq (hP₂ p hp)
  have hPU₂ : P ≤ Subgroup.normalizer (U₂ : Set G) := fun p hp => hP₂' p hp
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := c.exists_decomp_sup S ha
  have hcomp : ∀ p ∈ P, p * a₁ * p⁻¹ * a₁⁻¹ ∈ Zz ∧ p * a₂ * p⁻¹ * a₂⁻¹ ∈ Zz := by
    intro p hp
    have hEU : ∀ x ∈ uOfL22 T M, p * x * p⁻¹ ∈ uOfL22 T M := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hPU hp) x).mp hx
    have h1 := hfix p hp
    rw [comm_mul_of_abelian hcommU hEU (c.hU₁U ha₁) (c.hU₂U ha₂)] at h1
    have hx : p * a₁ * p⁻¹ * a₁⁻¹ ∈ U₁ :=
      U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPU₁ hp) a₁).mp ha₁) (U₁.inv_mem ha₁)
    have hy : p * a₂ * p⁻¹ * a₂⁻¹ ∈ U₂ :=
      U₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hP₂' p hp) a₂).mp ha₂) (U₂.inv_mem ha₂)
    set x := p * a₁ * p⁻¹ * a₁⁻¹ with hxdef
    set y := p * a₂ * p⁻¹ * a₂⁻¹ with hydef
    have hxZ : x ∈ Zz := by
      have e : x = (x * y) * y⁻¹ := by group
      have : x ∈ U₂ := by rw [e]; exact U₂.mul_mem (c.hZU₂ h1) (U₂.inv_mem hy)
      exact c.inf_U₂_eq ▸ ⟨hx, this⟩
    refine ⟨hxZ, ?_⟩
    have e : y = x⁻¹ * (x * y) := by group
    rw [e]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxZ) h1
  have hP₁triv : ∀ p ∈ P, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz := by
    by_cases ha₁Z : a₁ ∈ Zz
    ·
      have ha₂Z : a₂ ∉ Zz := by
        intro h2
        exact haZ (Subgroup.mul_mem _ ha₁Z h2)
      set a' := s⁻¹ * a₂ * s with ha'
      have ha'U₁ : a' ∈ U₁ := mem_conjSub.mp (c.hU₂ ▸ ha₂)
      have ha'Z : a' ∉ Zz := by
        intro hZ
        apply ha₂Z
        have := (Subgroup.mem_normalizer_iff.mp hsZ _).mp hZ
        have e : s * (s⁻¹ * a₂ * s) * s⁻¹ = a₂ := by group
        rwa [e] at this
      set P' : Subgroup G := conjSub s⁻¹ P with hP'
      have hP'perf : ⁅P', P'⁆ = P' := by
        rw [hP', conjSub_commutator, hP]
      have hP'Z : P' ≤ Subgroup.normalizer (Zz : Set G) := by
        have := conjSub_le_normalizer (g := s⁻¹) hPZ
        rwa [conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ hsZ)] at this
      have hP'U : P' ≤ Subgroup.normalizer (U₁ : Set G) := by
        have h1 := conjSub_le_normalizer (g := s⁻¹) hPU₂
        have e : conjSub s⁻¹ U₂ = U₁ := by rw [c.hU₂, conjSub_conjSub_inv]
        rw [e] at h1
        exact h1
      have hfix' : ∀ q ∈ P', q * a' * q⁻¹ * a'⁻¹ ∈ Zz := by
        intro q hq
        have hq' : s * q * s⁻¹ ∈ P := by
          have := mem_conjSub.mp hq
          simpa using this
        have h1 := (hcomp _ hq').2
        have e : q * a' * q⁻¹ * a'⁻¹ =
            s⁻¹ * ((s * q * s⁻¹) * a₂ * (s * q * s⁻¹)⁻¹ * a₂⁻¹) * s := by rw [ha']; group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsZ) _).mp h1
        simpa using this
      have hP'triv := c.perf_trivial hP'perf hP'Z hP'U ha'U₁ ha'Z hfix'
      intro p hp w hw
      have hpK' : s⁻¹ * p * s ∈ P' := by
        refine mem_conjSub.mpr ?_
        have e : s⁻¹⁻¹ * (s⁻¹ * p * s) * s⁻¹ = p := by group
        rw [e]; exact hp
      have hsp := hP'triv _ hpK' w hw
      have hpa'K : s⁻¹ * p * s ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ c.hsK) (hPK hp)) c.hsK
      have hpa'Z : s⁻¹ * p * s ∈ Subgroup.normalizer (Zz : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsZ) (hPZ hp)) hsZ
      have hpa'U₁ : conjSub (s⁻¹ * p * s) U₁ = U₁ :=
        c.conjSub_s_inner S (hPK hp) (hPU hp) (hPZ hp) (conjSub_eq_of_mem_normalizer (hPU₁ hp))
      have hcent' := c.centralizes_of_trivial₁ hpa'K hpa'Z (mem_normalizer_of_conjSub_eq hpa'U₁)
        (hP'triv _ hpK')
      have hcent : ∀ k ∈ K, p * k * p⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
        intro k hk
        have hk' : s⁻¹ * k * s ∈ K := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ c.hsK) k).mp hk
          simpa using this
        have h2 := hcent' _ hk'
        have e : p * k * p⁻¹ * k⁻¹ =
            s * ((s⁻¹ * p * s) * (s⁻¹ * k * s) * (s⁻¹ * p * s)⁻¹ * (s⁻¹ * k * s)⁻¹) * s⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K c.hsK) _).mp h2
      have hall := c.trivial_of_centralizes S (hPK hp) (hPU hp) (hPZ hp) hcent
      exact hall w (Subgroup.mem_sup_left hw)
    · exact c.perf_trivial hP hPZ hPU₁ ha₁ ha₁Z (fun p hp => (hcomp p hp).1)
  intro p hp y hy
  have hcent := c.centralizes_of_trivial₁ (hPK hp) (hPZ hp) (hPU₁ hp) (hP₁triv p hp)
  exact c.trivial_of_centralizes S (hPK hp) (hPU hp) (hPZ hp) hcent y hy

end PerfUK

end CFSG.Quasithin.ThreeC
