module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixROver
public import CFSG.Quasithin.EmptyFaithful.SBc17FixG2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRKer

public section

namespace CFSG.Quasithin.FixR

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G}
  {t : G}

theorem exists_mul_of_sup_eq_top {V : Type*} [Group V] (hc : ∀ a b : V, a * b = b * a)
    {A B : Subgroup V} (hsup : A ⊔ B = ⊤) (v : V) : ∃ a ∈ A, ∃ b ∈ B, a * b = v := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hv : v ∈ A ⊔ B := by
    rw [hsup]
    exact Subgroup.mem_top v
  exact Subgroup.mem_sup.mp hv

theorem comm_mem_pCoreOf_K (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    ∀ k ∈ oTwoUpper H, ∀ k' ∈ oTwoUpper H, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
  intro k hk k' hk'
  exact (mk_commute_iff (M := oTwoUpper H) ⟨k, hk⟩ ⟨k', hk'⟩).mp
    (SBc16.mul_comm_OTwoQuot_K S hp5 hred hdec _ _)

theorem relIndex_pCoreOf_K (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 25 := by
  have h := SBc16.card_OTwoQuot_K S hp5 hred hdec
  rw [Subgroup.relIndex, show (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H) =
    CFSG.Open.pCore 2 ↥(oTwoUpper H) from map_subtype_subgroupOf' _, Subgroup.index_eq_card]
  exact h

theorem pow_five_mem_pCoreOf_K (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    ∀ k ∈ oTwoUpper H, k ^ 5 ∈ pCoreOf 2 (oTwoUpper H) := by
  have hcomm := SBc16.mul_comm_OTwoQuot_K S hp5 hred hdec
  have hsup := SBc16.imageOTwoQuot_sup_eq_top S hred hdec
  have hV₁card : Nat.card ↥(imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)) = 5 := by
    have := SBc16.card_imageOTwoQuot_K hred hdec
    rwa [hp5] at this
  have hV₂card : Nat.card ↥(imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)) = 5 := by
    have := SBc16.card_imageOTwoQuot_K hred hdec.swap
    rwa [hp5] at this
  have hexp : ∀ v : OTwoQuot (oTwoUpper H), v ^ 5 = 1 := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_sup_eq_top hcomm hsup v
    have ha5 : a ^ 5 = 1 := by
      have := pow_card_eq_one' (G := imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)) (x := ⟨a, ha⟩)
      rw [hV₁card] at this
      exact congrArg Subtype.val this
    have hb5 : b ^ 5 = 1 := by
      have := pow_card_eq_one' (G := imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)) (x := ⟨b, hb⟩)
      rw [hV₂card] at this
      exact congrArg Subtype.val this
    rw [(show Commute a b from hcomm a b).mul_pow, ha5, hb5, one_mul]
  intro k hk
  refine (mk_eq_one_iff_mem_pCoreOf (⟨k, hk⟩ ^ 5 : ↥(oTwoUpper H))).mp ?_
  rw [QuotientGroup.mk_pow]
  exact hexp _

theorem noFive_range (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∀ α ∈ (SBc17.psiHom hKG).range, orderOf α ≠ 5 := by
  intro α hα hα5
  obtain ⟨⟨g, hg⟩, rfl⟩ := hα
  have hab := comm_mem_pCoreOf_K S hp5 hred hdec
  have hHT := hred.isHTM
  have hTH : T ≤ H := hHT.1.1
  have hHΓ : H ≤ mcOf T := S.le_mcOf hHT
  have hTH' : IsSylowTwoOf T H := isSylowTwoOf_of_le151 S.hyp.sylow hTH
  have hTΓ : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_le151 S.hyp.sylow (hTH.trans hHΓ)
  obtain ⟨c, hcC, hcn⟩ := exists_mul_mem_normalizer hTH' hTΓ hHΓ hKG hab hg
  have hcΓ : c ∈ mcOf T := hcC.1
  have hnΓ : c⁻¹ * g ∈ mcOf T := (mcOf T).mul_mem ((mcOf T).inv_mem hcΓ) hg
  have hψc : SBc17.psiHom hKG ⟨c, hcΓ⟩ = 1 :=
    (SBc16.actHom_eq_one_iff _ (hKG hcΓ)).mpr fun k hk => (SBc14.mem_kerAct.mp hcC.2).2 k hk
  have hψn : SBc17.psiHom hKG ⟨c⁻¹ * g, hnΓ⟩ = SBc17.psiHom hKG ⟨g, hg⟩ := by
    have e : (⟨c⁻¹ * g, hnΓ⟩ : ↥(mcOf T)) = (⟨c, hcΓ⟩ : ↥(mcOf T))⁻¹ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_inv, hψc, inv_one, one_mul]
  have hn5 : ∀ k ∈ oTwoUpper H, (c⁻¹ * g) ^ 5 * k * ((c⁻¹ * g) ^ 5)⁻¹ * k⁻¹ ∈
      pCoreOf 2 (oTwoUpper H) := by
    have h1 : (SBc17.psiHom hKG ⟨c⁻¹ * g, hnΓ⟩) ^ 5 = 1 := by
      rw [hψn]
      have := pow_orderOf_eq_one (SBc17.psiHom hKG ⟨g, hg⟩)
      rwa [hα5] at this
    have h2 : (⟨(c⁻¹ * g) ^ 5, (mcOf T).pow_mem hnΓ 5⟩ : ↥(mcOf T)) =
        (⟨c⁻¹ * g, hnΓ⟩ : ↥(mcOf T)) ^ 5 := rfl
    have h3 : SBc17.psiHom hKG ⟨(c⁻¹ * g) ^ 5, (mcOf T).pow_mem hnΓ 5⟩ = 1 := by
      rw [h2, map_pow]
      exact h1
    exact (SBc16.actHom_eq_one_iff _ (hKG ((mcOf T).pow_mem hnΓ 5))).mp h3
  have hn1 : ∃ k ∈ oTwoUpper H, (c⁻¹ * g) * k * (c⁻¹ * g)⁻¹ * k⁻¹ ∉ pCoreOf 2 (oTwoUpper H) := by
    by_contra hcon
    push Not at hcon
    have h1 : SBc17.psiHom hKG ⟨c⁻¹ * g, hnΓ⟩ = 1 :=
      (SBc16.actHom_eq_one_iff _ (hKG hnΓ)).mpr hcon
    rw [hψn] at h1
    have h2 : orderOf (SBc17.psiHom hKG ⟨g, hg⟩) = 1 := orderOf_eq_one_iff.mpr h1
    rw [hα5] at h2
    omega
  set n : G := c⁻¹ * g with hn
  have hnK : n ∈ Subgroup.normalizer (oTwoUpper H : Set G) := hKG hnΓ
  have hnQ : n ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    have : c⁻¹ * g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := hcn
    exact this
  set Hp : Subgroup G := H ⊔ Subgroup.zpowers n with hHp
  have hHpK : Hp ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le (le_normalizer_oTwoUpper H) ((Subgroup.zpowers_le).mpr hnK)
  have hHpQ : Hp ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 H) ((Subgroup.zpowers_le).mpr hnQ)
  have hQHp : pCoreOf 2 H ≤ pCoreOf 2 Hp :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 H).trans le_sup_left) hHpQ (pCoreOf_isPGroup 2 H)
  have hHpHTM : IsHTM T M Hp :=
    ⟨⟨hTH.trans le_sup_left, fun h => hHT.1.2 (le_bot_iff.mp (h ▸ hQHp))⟩,
      fun h => hHT.2 (le_sup_left.trans h)⟩
  have h98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hHpHTM)).2
  have hL1 : L₁Of (yOfL22 T M) (quasithinOmegaOneCenter T) = ⊥ :=
    (lOne_eq_L₁Of _ _).symm.trans S.lOne_eq_bot
  have hKer : ∀ b ∈ T, (∀ k ∈ oTwoUpper H, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) →
      b ∈ pCoreOf 2 Hp := by
    intro b hbT hb
    have hbO : b ∈ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
      ((hTH'.le.trans (le_normalizer_oTwoUpper H)).trans
        (normalizer_le_normalizer_pCoreOf 2 _)) hbT
    exact hQHp (inf_kerAct_le_pCoreOf hTH' hab ⟨hbT, SBc14.mem_kerAct.mpr ⟨hbO, hb⟩⟩)
  exact false_of_f9 h98 hL1 (hTH.trans le_sup_left) ((oTwoUpper_le H).trans le_sup_left) hHpK hab
    (relIndex_pCoreOf_K S hp5 hred hdec) (pow_five_mem_pCoreOf_K S hp5 hred hdec) hKer
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers n)) hn5 hn1

theorem input14615FixR_proved : SBc17.Input14615FixR := by
  intro G _ _ T M S H PQ p hred _ H₀ H₁ H₂ t hdec hctx hCz _
  have hKG := SBc17.mcOf_le_normalizer_oTwoUpper hCz
  exact SBc17.gap3Fix_of_noFive S hctx.1 hred hdec hKG (noFive_range S hctx.1 hred hdec hKG)

end CFSG.Quasithin.FixR
