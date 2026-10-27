module

public import CFSG.Quasithin.MS93.S46TypeLin
public import CFSG.Quasithin.MS93.S4A42Coc

public section

namespace CFSG.Quasithin.MS93.S46.I464

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.MS93.S4A
open scoped Matrix commutatorElement

section SL3

variable {F : Type} [Field F]

theorem sub_mem_pt0_of_mem_sStar {s : SL3 F} (hs : s ∈ sStar) {x : Fin 3 → F}
    (hx : x ∈ ln01) : (s : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ pt0 := by
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hs
  rw [mem_ln01] at hx
  rw [mem_pt0]
  simp [coe_uniTri, dotProduct, Fin.sum_univ_three, hx]

theorem sub_mem_fixN_of_mem_commN [Finite F] [CharP F 2] {P : Subgroup (SL3 F)}
    (hP : IsPGroup 2 P) {g : SL3 F} (hg : g ∈ P) {x : Fin 3 → F} (hx : x ∈ commN P) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ fixN P := by
  obtain ⟨y, hy⟩ := exists_conj_le_sStar hP
  have hx' : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ commN (P.map (MulAut.conj y).toMonoidHom) := by
    rw [commN_map_conj]
    exact ⟨x, hx, rfl⟩
  have hg' : (MulAut.conj y).toMonoidHom g ∈ (sStar : Subgroup (SL3 F)) :=
    hy (Subgroup.mem_map_of_mem _ hg)
  have h1 := pt0_le_fixN_of_le_sStar hy
    (sub_mem_pt0_of_mem_sStar hg' (commN_le_ln01_of_le_sStar hy hx'))
  rw [fixN_map_conj, Submodule.mem_map_equiv] at h1
  have e : ((MulAut.conj y).toMonoidHom g : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
      (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← coe_mul_SL3, ← coe_mul_SL3, mul_assoc (y * g), inv_mul_cancel, mul_one]
  rw [e, ← Matrix.mulVec_sub] at h1
  change ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ
    ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x)) ∈ fixN P at h1
  rwa [inv_mulVec_mulVec_SL3] at h1

theorem commN_le_fixN_of_two_le_finrank [Finite F] [CharP F 2] {P : Subgroup (SL3 F)}
    (hP : IsPGroup 2 P) (h2 : 2 ≤ Module.finrank F (fixN P)) : commN P ≤ fixN P := by
  rw [commN, Submodule.span_le]
  rintro _ ⟨g, hg, x, rfl⟩
  have h3 := Submodule.finrank_le (fixN P)
  rw [Module.finrank_fin_fun] at h3
  rcases (by omega : Module.finrank F (fixN P) = 2 ∨ Module.finrank F (fixN P) = 3) with e | e
  · obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact sub_mem_of_finrank_eq_two hk' e (fun y hy => by rw [hy g hg]; exact hy) x
  · have htop : fixN P = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [e, Module.finrank_fin_fun])
    rw [htop]
    trivial

theorem commN_le_fixN_of_finrank_le_one [CharP F 2] {P : Subgroup (SL3 F)}
    (hP : IsPGroup 2 P) (h1 : Module.finrank F (commN P) ≤ 1) : commN P ≤ fixN P := by
  intro x hx g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact mulVec_eq_of_finrank_le_one hk' h1
    (fun y hy => mulVec_mem_commN_of_normalizes (fun e he => P.mul_mem (P.mul_mem hg he)
      (P.inv_mem hg)) hy) hx

theorem card_le_of_finrank [Finite F] {E : Subgroup (SL3 F)}
    (h2 : 2 ≤ Module.finrank F (fixN E)) (h1 : Module.finrank F (commN E) ≤ 1) :
    Nat.card E ≤ Nat.card F := by
  have h3 := Submodule.finrank_le (fixN E)
  rw [Module.finrank_fin_fun] at h3
  have hle : (3 - Module.finrank F (fixN E)) * Module.finrank F (commN E) ≤ 1 := by
    rcases (by omega : Module.finrank F (commN E) = 0 ∨ Module.finrank F (commN E) = 1) with
      e | e <;> rw [e] <;> omega
  have hq : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  calc Nat.card E ≤ Nat.card F ^ ((3 - Module.finrank F (fixN E)) *
        Module.finrank F (commN E)) := card_le_pow_finrank E
    _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right hq hle
    _ = Nat.card F := pow_one _

end SL3

section Dict

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {ψ : ↥K →* ↥(StatedSL 3 F)} (hψ : IsSumOfNaturalModulesVia K V ⊥ ψ false 1)
include hψ

theorem commutator_le_centralizer_of_commN_le_fixN {A B : Subgroup G} (hA : A ≤ K)
    (hB : B ≤ K) (h : commN (natImage ψ B) ≤ fixN (natImage ψ A)) :
    ⁅V, B⁆ ≤ Subgroup.centralizer (A : Set G) := by
  have hVB : ⁅V, B⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hB.trans hψ.1)
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hx := h ((mem_commutator_iff_natVec hψ hB ⟨w, hVB hw⟩).mp hw)
  exact (commute_iff_natVec hψ ⟨a, hA ha⟩ ⟨w, hVB hw⟩).mpr
    (hx _ (mem_natImage.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩))

theorem commN_le_fixN_of_commutator_le_centralizer {A B : Subgroup G} (hB : B ≤ K)
    (h : ⁅V, B⁆ ≤ Subgroup.centralizer (A : Set G)) :
    commN (natImage ψ B) ≤ fixN (natImage ψ A) := by
  intro x hx g hg
  obtain ⟨u, rfl⟩ := natVec_surjective hψ x
  obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
  have hu := h ((mem_commutator_iff_natVec hψ hB u).mpr hx)
  exact (commute_iff_natVec hψ a u).mp (Subgroup.mem_centralizer_iff.mp hu _ haA)

theorem commutator_commutator_le_centralizer [Finite F] [CharP F 2] {A : Subgroup G}
    (hA : A ≤ K) (hP : IsPGroup 2 (natImage ψ A)) :
    ⁅⁅V, A⁆, A⁆ ≤ Subgroup.centralizer (A : Set G) := by
  have hVA : ⁅V, A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans hψ.1)
  rw [Subgroup.commutator_le]
  intro w hw a ha
  have hmem : ⁅w, a⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator (hVA hw) ha)
  have hx := (mem_commutator_iff_natVec hψ hA ⟨w, hVA hw⟩).mp hw
  have hg : toSL3 ψ ⟨a, hA ha⟩ ∈ natImage ψ A := mem_natImage.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩
  have hfix : natVec hψ ⟨_, hmem⟩ ∈ fixN (natImage ψ A) := by
    rw [natVec_commutator hψ ⟨a, hA ha⟩ ⟨w, hVA hw⟩ ⟨_, hmem⟩ rfl, ← neg_sub]
    exact Submodule.neg_mem _ (sub_mem_fixN_of_mem_commN hP hg hx)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (commute_iff_natVec hψ ⟨b, hA hb⟩ ⟨_, hmem⟩).mpr
    (hfix _ (mem_natImage.mpr ⟨⟨b, hA hb⟩, hb, rfl⟩))

theorem card_commutator_eq_pow [Finite F] {A : Subgroup G} (hA : A ≤ K) :
    Nat.card ↥⁅V, A⁆ = Nat.card F ^ Module.finrank F (commN (natImage ψ A)) := by
  rw [card_commutator_eq hψ hA, Module.natCard_eq_pow_finrank (K := F)]

theorem card_inf_centralizer_eq_pow [Finite F] {A : Subgroup G} (hA : A ≤ K) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card F ^ Module.finrank F (fixN (natImage ψ A)) := by
  rw [card_inf_centralizer_eq hψ hA, Module.natCard_eq_pow_finrank (K := F)]

end Dict

end CFSG.Quasithin.MS93.S46.I464
