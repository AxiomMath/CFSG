module

public import CFSG.Quasithin.EmptyFaithful.SBc13Pair
public import CFSG.Quasithin.EmptyFaithful.S146P12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc14

section Ker

variable {G : Type} [Group G]

def kerAct (K O : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (O : Set G) ∧ ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ O}
  one_mem' := ⟨Subgroup.one_mem _, fun k _ => by simp⟩
  mul_mem' := by
    rintro y z ⟨hyO, hy⟩ ⟨hzO, hz⟩
    refine ⟨Subgroup.mul_mem _ hyO hzO, fun k hk => ?_⟩
    have e : y * z * k * (y * z)⁻¹ * k⁻¹ =
        (y * (z * k * z⁻¹ * k⁻¹) * y⁻¹) * (y * k * y⁻¹ * k⁻¹) := by group
    rw [e]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp hyO _).mp (hz k hk)) (hy k hk)
  inv_mem' := by
    rintro y ⟨hyO, hy⟩
    refine ⟨Subgroup.inv_mem _ hyO, fun k hk => ?_⟩
    have e : y⁻¹ * k * y⁻¹⁻¹ * k⁻¹ = y⁻¹ * (y * k * y⁻¹ * k⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyO) _).mp (O.inv_mem (hy k hk))

theorem mem_kerAct {K O : Subgroup G} {y : G} :
    y ∈ kerAct K O ↔
      y ∈ Subgroup.normalizer (O : Set G) ∧ ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ O := Iff.rfl

theorem le_normalizer_kerAct {K O N : Subgroup G} (hK : N ≤ Subgroup.normalizer (K : Set G))
    (hO : N ≤ Subgroup.normalizer (O : Set G)) :
    N ≤ Subgroup.normalizer (kerAct K O : Set G) := by
  have key : ∀ g ∈ N, ∀ y ∈ kerAct K O, g * y * g⁻¹ ∈ kerAct K O := by
    intro g hg y hy
    obtain ⟨hyO, hyc⟩ := mem_kerAct.mp hy
    refine mem_kerAct.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hO hg) hyO)
      (Subgroup.inv_mem _ (hO hg)), fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hK (N.inv_mem hg)) k).mp hk
    have h1 := (Subgroup.mem_normalizer_iff.mp (hO hg) _).mp (hyc _ hk')
    have e : g * y * g⁻¹ * k * (g * y * g⁻¹)⁻¹ * k⁻¹ =
        g * (y * (g⁻¹ * k * g⁻¹⁻¹) * y⁻¹ * (g⁻¹ * k * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun h => ?_⟩
  have := key g⁻¹ (N.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem mem_normalizer_inf {A B : Subgroup G} {k : G} (hA : k ∈ Subgroup.normalizer (A : Set G))
    (hB : k ∈ Subgroup.normalizer (B : Set G)) :
    k ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [Subgroup.mem_inf]
  rw [hA h, hB h]

end Ker

section Basic

variable {G : Type} [Group G] {T M H H₁ H₂ K₁ K₂ : Subgroup G} {s : G}

theorem mcOf_le_normalizer_kz (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  rw [← hset.kz]
  exact le_normalizer_conjClosure _ _

theorem mcOf_le_normalizer_pCoreOf_kz (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    mcOf T ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ K₂) : Set G) :=
  (mcOf_le_normalizer_kz hset).trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem commutator_mem_pCoreOf_kz (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) {R : Subgroup G}
    (hR2 : IsPGroup 2 R) (hRG : R ≤ mcOf T) (hRK : K₁ ⊔ K₂ ≤ Subgroup.normalizer (R : Set G))
    {x k : G} (hx : x ∈ R) (hk : k ∈ K₁ ⊔ K₂) :
    x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (K₁ ⊔ K₂) := by
  have hxK : x * k * x⁻¹ ∈ K₁ ⊔ K₂ :=
    (Subgroup.mem_normalizer_iff.mp (mcOf_le_normalizer_kz hset (hRG hx)) k).mp hk
  have h1 : k * x⁻¹ * k⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hRK hk) x⁻¹).mp (R.inv_mem hx)
  have hc : x * k * x⁻¹ * k⁻¹ ∈ R := by
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact R.mul_mem hx h1
  have hcK : x * k * x⁻¹ * k⁻¹ ∈ K₁ ⊔ K₂ := (K₁ ⊔ K₂).mul_mem hxK ((K₁ ⊔ K₂).inv_mem hk)
  have hle : R ⊓ (K₁ ⊔ K₂) ≤ pCoreOf 2 (K₁ ⊔ K₂) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k' hk' => mem_normalizer_inf (hRK hk') (Subgroup.le_normalizer hk'))
      (hR2.to_le inf_le_left)
  exact hle ⟨hc, hcK⟩

end Basic

section Main

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem kerAct_le_g2 (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    kerAct (K₁ ⊔ K₂) (pCoreOf 2 (K₁ ⊔ K₂)) ≤ g2_14615 K₂ := by
  intro y hy
  obtain ⟨-, hyc⟩ := mem_kerAct.mp hy
  have hKzN : K₁ ⊔ K₂ ≤ g2_14615 K₂ := by
    rw [← hset.kz]
    exact kz_le_g2_14615 hdec hset
  set O := pCoreOf 2 (K₁ ⊔ K₂) with hO
  have hOK : O ≤ K₁ ⊔ K₂ := pCoreOf_le 2 _
  have hle : conjSub y K₂ ≤ O ⊔ K₂ := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ : ∃ k ∈ K₂, z = y * k * y⁻¹ :=
      ⟨y⁻¹ * z * y, mem_conjSub.mp hz, by group⟩
    have hc := hyc k (Subgroup.mem_sup_right hk)
    have e : y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact (O ⊔ K₂).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hk)
  have hRN : O ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set G) :=
    sup_le (hOK.trans hKzN) Subgroup.le_normalizer
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 _
  have hOup : oTwoUpper (O ⊔ K₂) ≤ K₂ :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hRN) hO2 le_sup_left
      (by rw [sup_comm])
  have hperf : oTwoUpper (conjSub y K₂) = conjSub y K₂ := by
    rw [oTwoUpper_conjSub_P, hset.perf₂]
  have hle' : conjSub y K₂ ≤ K₂ :=
    calc conjSub y K₂ = oTwoUpper (conjSub y K₂) := hperf.symm
      _ ≤ oTwoUpper (O ⊔ K₂) := oTwoUpper_mono hle
      _ ≤ K₂ := hOup
  exact CosetGeom.mem_normalizer_of_conjSub_eq
    (Subgroup.eq_of_le_of_card_ge hle' (by rw [SBc13.card_conjSub']))

theorem pCoreOf_mcOf_le_kerAct (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    pCoreOf 2 (mcOf T) ≤ kerAct (K₁ ⊔ K₂) (pCoreOf 2 (K₁ ⊔ K₂)) := by
  have hKG : K₁ ⊔ K₂ ≤ mcOf T := by
    rw [← hset.kz]
    exact SBc13.kz_le_mcOf S hred
  intro x hx
  exact mem_kerAct.mpr ⟨mcOf_le_normalizer_pCoreOf_kz hset (pCoreOf_le 2 _ hx), fun k hk =>
    commutator_mem_pCoreOf_kz hset (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _)
      (fun k' hk' => le_normalizer_pCoreOf 2 (mcOf T) (hKG hk')) hx hk⟩

theorem pCoreOf_mcOf_le_g2 (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    pCoreOf 2 (mcOf T) ≤ g2_14615 K₂ :=
  (pCoreOf_mcOf_le_kerAct S hred hset).trans (kerAct_le_g2 hdec hset)

theorem pCoreOf_mcOf_le_g12 (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    pCoreOf 2 (mcOf T) ≤ g12_14615 T K₂ :=
  le_inf (pCoreOf_le 2 _) (pCoreOf_mcOf_le_g2 S hred hdec hset)

theorem pCoreOf_g12_eq (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    pCoreOf 2 (g12_14615 T K₂) = pCoreOf 2 (mcOf T) := by
  apply le_antisymm
  · set R := pCoreOf 2 (g12_14615 T K₂) with hR
    set C : Subgroup G := kerAct (K₁ ⊔ K₂) (pCoreOf 2 (K₁ ⊔ K₂)) ⊓ mcOf T with hC
    have hKG : K₁ ⊔ K₂ ≤ mcOf T := by
      rw [← hset.kz]
      exact SBc13.kz_le_mcOf S hred
    have hKzN : K₁ ⊔ K₂ ≤ g2_14615 K₂ := by
      rw [← hset.kz]
      exact kz_le_g2_14615 hdec hset
    have hKg12 : K₁ ⊔ K₂ ≤ g12_14615 T K₂ := le_inf hKG hKzN
    have hRn : g12_14615 T K₂ ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
    have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 _
    have hRG₁₂ : R ≤ g12_14615 T K₂ := pCoreOf_le 2 _
    have hRC : R ≤ C := by
      refine le_inf (fun x hx => mem_kerAct.mpr ⟨?_, fun k hk => ?_⟩) (hRG₁₂.trans inf_le_left)
      · exact mcOf_le_normalizer_pCoreOf_kz hset (hRG₁₂ hx).1
      · exact commutator_mem_pCoreOf_kz hset hR2 (hRG₁₂.trans inf_le_left) (fun k' hk' => hRn (hKg12 hk'))
          hx hk
    have hCg12 : C ≤ g12_14615 T K₂ := fun y hy => ⟨hy.2, kerAct_le_g2 hdec hset hy.1⟩
    have hCnorm : mcOf T ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
      mem_normalizer_inf (le_normalizer_kerAct (mcOf_le_normalizer_kz hset)
        (mcOf_le_normalizer_pCoreOf_kz hset) hg) (Subgroup.le_normalizer hg)
    have hRC' : R ≤ pCoreOf 2 C := le_pCoreOf_of_le_normalizer 2 hRC (hCg12.trans hRn) hR2
    exact hRC'.trans (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans inf_le_right)
      (hCnorm.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C))
  · exact le_pCoreOf_of_le_normalizer 2 (pCoreOf_mcOf_le_g12 S hred hdec hset)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 (mcOf T))) (pCoreOf_isPGroup 2 _)

end Main

end SBc14

end CFSG.Quasithin
