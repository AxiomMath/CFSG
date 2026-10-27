module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42PData
public import CFSG.Quasithin.Vol2.Asc94.He42Alg
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaGen1

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD
open CFSG.Quasithin.H13.F431.U42Aut (altW altW_zero)

variable {G : Type} [Group G] [Finite G]

private lemma he42bn_altW_one (r r' : G) : altW r r' 1 = r := by
  show r * altW r' r 0 = r
  rw [altW_zero, mul_one]

private lemma he42bn_altW_two (r r' : G) : altW r r' 2 = r * r' := by
  show r * (r' * altW r r' 0) = r * r'
  rw [altW_zero, mul_one]

private lemma he42bn_card_map {L K A J R : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hψ : PData L K A J ψ) (hRL : R ≤ L) (hRA : A ⊓ R = ⊥) :
    Nat.card ((R.subgroupOf L).map ψ) = Nat.card R := by
  have hinj : Function.Injective (ψ.comp (R.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hfx
    have hker : x ∈ ψ.ker := MonoidHom.mem_ker.mpr hfx
    rw [hψ.ker, Subgroup.mem_subgroupOf] at hker
    have hxR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
    have h1 : (x : G) ∈ A ⊓ R := Subgroup.mem_inf.mpr ⟨hker, hxR⟩
    rw [hRA, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hmap : (R.subgroupOf L).map ψ = (ψ.comp (R.subgroupOf L).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv

theorem HeSetup.bnpair (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) {y₁ y₂ : G}
    (hY : YSpec S y₁ y₂) (hR : S.StepR y₁ y₂) {l₁ l₂ : G} (hl : WSpec S y₁ y₂ l₁ l₂)
    (hbraid : (l₁ * l₂) ^ 3 = 1) :
    ∃ U₁ U₂ : List G, CFSG.Quasithin.H13.F431.U42Aut.BNPairGen S.K S.L1 S.L2 l₁ l₂ U₁ U₂ 3 := by
  obtain ⟨⟨ψ₁, hψ₁⟩, ψ₂, hψ₂⟩ := hP
  obtain ⟨⟨hR₁card, hR₁A⟩, ⟨hR₂card, hR₂A⟩, hRz₁, hRz₂⟩ := hR
  have h1 : y₁ ^ 3 = 1 := by rw [← hY.ord₁]; exact pow_orderOf_eq_one y₁
  have h2 : y₂ ^ 3 = 1 := by rw [← hY.ord₂]; exact pow_orderOf_eq_one y₂
  have hR₁J : S.A' ⊓ centralizer ({y₁} : Set G) ≤ S.J := inf_le_left.trans hB.A'_le_J
  have hR₂J : S.A ⊓ centralizer ({y₂} : Set G) ≤ S.J := inf_le_left.trans hB.A_le_J
  have hR₁L : S.A' ⊓ centralizer ({y₁} : Set G) ≤ S.L1 :=
    hR₁J.trans (hB.J_le_K.trans hB.K_le_L1)
  have hR₂L : S.A ⊓ centralizer ({y₂} : Set G) ≤ S.L2 :=
    hR₂J.trans (hB.J_le_K.trans hB.K_le_L2)
  obtain ⟨U₁, hU₁R, hr1⟩ := PData.exists_rankOne hψ₁ hR₁J
    ((he42bn_card_map hψ₁ hR₁L hR₁A).trans hR₁card) hl.mem₁ hl.nmem₁ hl.sq₁
  obtain ⟨U₂, hU₂R, hr2⟩ := PData.exists_rankOne hψ₂ hR₂J
    ((he42bn_card_map hψ₂ hR₂L hR₂A).trans hR₂card) hl.mem₂ hl.nmem₂ hl.sq₂
  have hcent₁ : ∀ u ∈ U₁, u ∈ S.A' ∧ u * y₁ = y₁ * u := fun u hu => by
    obtain ⟨huA, hucent⟩ := Subgroup.mem_inf.mp (hU₁R u hu)
    exact ⟨huA, Subgroup.mem_centralizer_singleton_iff.mp hucent⟩
  have hcent₂ : ∀ u ∈ U₂, u ∈ S.A ∧ u * y₂ = y₂ * u := fun u hu => by
    obtain ⟨huA, hucent⟩ := Subgroup.mem_inf.mp (hU₂R u hu)
    exact ⟨huA, Subgroup.mem_centralizer_singleton_iff.mp hucent⟩
  have hl₂A' : ∀ a ∈ S.A', l₂⁻¹ * a * l₂ ∈ S.A' := fun a ha =>
    (Subgroup.mem_normalizer_iff''.mp (hB.L2_le_normalizer hl.mem₂) a).mp ha
  have hl₁A : ∀ a ∈ S.A, l₁⁻¹ * a * l₁ ∈ S.A := fun a ha =>
    (Subgroup.mem_normalizer_iff''.mp (hB.L1_le_normalizer hl.mem₁) a).mp ha
  have hconj₂ : l₂ * y₁ * l₂⁻¹ = (y₁ * y₂)⁻¹ :=
    CFSG.Quasithin.A94.He42Alg.l2_conj_y1 hY.comm h2 hl.cent₂ hl.inv₂
  have hconj₁ : l₁ * y₂ * l₁⁻¹ = (y₁ * y₂)⁻¹ :=
    CFSG.Quasithin.A94.He42Alg.l1_conj_y2 hY.comm h1 hl.cent₁ hl.inv₁
  have hbr : l₁ * (l₂ * l₁) = l₂ * (l₁ * l₂) := by
    have hXY : (l₁ * (l₂ * l₁)) * (l₂ * (l₁ * l₂)) = 1 :=
      (by simp only [pow_three', mul_assoc] :
        (l₁ * (l₂ * l₁)) * (l₂ * (l₁ * l₂)) = (l₁ * l₂) ^ 3).trans hbraid
    have hYY : (l₂ * (l₁ * l₂)) * (l₂ * (l₁ * l₂)) = 1 := by
      calc (l₂ * (l₁ * l₂)) * (l₂ * (l₁ * l₂)) = (l₂ * l₁) * (l₂ * l₂) * (l₁ * l₂) := by group
        _ = (l₂ * l₁) * (l₁ * l₂) := by rw [hl.sq₂, mul_one]
        _ = (l₂ * (l₁ * l₁)) * l₂ := by group
        _ = 1 := by rw [hl.sq₁, mul_one, hl.sq₂]
    exact (eq_inv_of_mul_eq_one_left hXY).trans (inv_eq_of_mul_eq_one_right hYY)
  refine ⟨U₁, U₂, hr1, hr2, by norm_num, ?_, ?_, ?_⟩
  ·
    show l₁ * (l₂ * (l₁ * 1)) = l₂ * (l₁ * (l₂ * 1))
    simpa only [mul_one] using hbr
  ·
    intro k hk u hu
    obtain ⟨huA', huy⟩ := hcent₁ u hu
    have huK : u ∈ S.K := hB.J_le_K (hB.A'_le_J huA')
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · rw [altW_zero, inv_one, one_mul, mul_one]
      exact huK
    · rw [he42bn_altW_one]
      exact hB.J_le_K (hB.A'_le_J (hl₂A' u huA'))
    · rw [he42bn_altW_two]
      have hwZ : l₂⁻¹ * u * l₂ ∈ S.Z :=
        hRz₁ _ (hl₂A' u huA') (CFSG.Quasithin.A94.He42Alg.conj_comm_l2 hl.sq₂ hconj₂ huy)
      have hwA : l₁⁻¹ * (l₂⁻¹ * u * l₂) * l₁ ∈ S.A := hl₁A _ (hB.Z_le_A hwZ)
      have e : (l₂ * l₁)⁻¹ * u * (l₂ * l₁) = l₁⁻¹ * (l₂⁻¹ * u * l₂) * l₁ := by group
      rw [e]
      exact hB.J_le_K (hB.A_le_J hwA)
  ·
    intro k hk u hu
    obtain ⟨huA, huy⟩ := hcent₂ u hu
    have huK : u ∈ S.K := hB.J_le_K (hB.A_le_J huA)
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · rw [altW_zero, inv_one, one_mul, mul_one]
      exact huK
    · rw [he42bn_altW_one]
      exact hB.J_le_K (hB.A_le_J (hl₁A u huA))
    · rw [he42bn_altW_two]
      have hwZ : l₁⁻¹ * u * l₁ ∈ S.Z :=
        hRz₂ _ (hl₁A u huA) (CFSG.Quasithin.A94.He42Alg.conj_comm_l1 hl.sq₁ hconj₁ huy)
      have hwA' : l₂⁻¹ * (l₁⁻¹ * u * l₁) * l₂ ∈ S.A' := hl₂A' _ (hB.Z_le_A' hwZ)
      have e : (l₁ * l₂)⁻¹ * u * (l₁ * l₂) = l₂⁻¹ * (l₁⁻¹ * u * l₁) * l₂ := by group
      rw [e]
      exact hB.J_le_K (hB.A'_le_J hwA')

end CFSG.Quasithin.A94.He42
