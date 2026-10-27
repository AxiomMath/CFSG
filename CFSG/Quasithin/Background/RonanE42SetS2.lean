module

public import CFSG.Quasithin.Background.RonanE42SetS

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {K Y : Subgroup G} (hYn : ∀ h ∈ K, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    {k : G} (hk : k ∈ K) : k ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => hYn k hk z hz, fun hz => ?_⟩
  have := hYn k⁻¹ (K.inv_mem hk) _ hz
  simpa [mul_assoc] using this

theorem mQuot_le_pRank_fStarMod {K A : Subgroup G} (hAX : A ≤ fStarPre K)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    mQuot A (A ⊓ pCoreOf 2 K) ≤ CFSG.Open.pRank 2 (fStarMod K) := by
  have hAK : A ≤ K := hAX.trans (Subgroup.map_subtype_le _)
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA2 (a : G) a.2)⟩
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set E := (A.subgroupOf K).map π with hE
  have hcard : Nat.card E = 2 ^ mQuot A (A ⊓ pCoreOf 2 K) := by
    have h1 := Subgroup.relIndex_ker (K := A.subgroupOf K) (f := π)
    rw [hπ, QuotientGroup.ker_mk'] at h1
    have h2 := Subgroup.relIndex_map_map_of_injective (f := K.subtype) (CFSG.pCore 2 ↥K)
      (A.subgroupOf K) K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK] at h2
    rw [hE, ← h1, ← h2]
    show (pCoreOf 2 K).relIndex A = _
    rw [← Subgroup.inf_relIndex_left (H := A) (K := pCoreOf 2 K)]
    exact relIndex_eq_two_pow hAp _
  have hEl : IsElemAbelian 2 E := by
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
    unfold IsElemAbelian
    refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu2 : u ^ 2 = 1 :=
      Subtype.ext (by simpa using hA2 (u : G) (Subgroup.mem_subgroupOf.mp hu))
    rw [← map_pow, hu2, map_one]
  have hEF : E ≤ fStarMod K := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 (hAX (Subgroup.mem_subgroupOf.mp hu))
    have : y = u := Subtype.ext hyu
    rw [← this]
    exact Subgroup.mem_comap.1 hy
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K),
      E ≤ fStarMod K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card (↥K ⧸ CFSG.pCore 2 ↥K), ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    exact (k.lt_two_pow_self.le).trans
      (hE'.symm.trans_le (Subgroup.card_le_card_group (H := E')))
  unfold CFSG.Open.pRank
  exact le_csSup hbdd ⟨E, hEF, hEl, hcard⟩

theorem Om_le_mQuot_bot {V : Type} [CommGroup V] {ρ : G →* MulAut V} (hρ : Function.Injective ρ)
    {n : ℕ} {A : Subgroup G} (hA : Om ρ n A) : n ≤ mQuot A ⊥ := by
  by_contra h
  push Not at h
  have hF := hA.2.2.2 ⊥ bot_le h
  apply hA.1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply hρ
  rw [map_one]
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ Fx ρ ⊥ := mem_Fx.2 fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one, MulAut.one_apply]
  rw [hF] at hv
  exact mem_Fx.1 hv a ha

theorem mQuot_bot_le_pRank {A : Subgroup G} (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    mQuot A ⊥ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA2 (a : G) a.2)⟩
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G,
      E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    exact (k.lt_two_pow_self.le).trans
      (hE'.symm.trans_le (Subgroup.card_le_card_group (H := E')))
  unfold CFSG.Open.pRank
  refine le_csSup hbdd ⟨A, le_top,
    ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hAc _ a.2 _ b.2), hA2⟩, ?_⟩
  have h := relIndex_eq_two_pow hAp ⊥
  rwa [Subgroup.relIndex_bot_left] at h

theorem aParam_le_pRank {V : Type} [CommGroup V] [Finite V] {ρ : G →* MulAut V}
    (hρ : Function.Injective ρ) : aParam ρ.range ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
  apply aParam_le_of_aSet_empty
  intro A' hA'
  have hA := Om_comap_of_mem_aSet hρ hA'
  have h1 := Om_le_mQuot_bot hρ hA
  have h2 := mQuot_bot_le_pRank hA.2.1 hA.2.2.1
  omega

theorem xt_le_stabV_of_mem {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    {D A : Subgroup G} (hA : A ∈ Ω) (hDA : D ≤ A) (hDT : D ≤ T) (hDX : D ≤ fStarPre K)
    (hDR : ¬ D ≤ pCoreOf 2 K) {j c : ℕ} (hmD : mQuot A D ≤ j)
    (hjc : j + CFSG.Open.pRank 2 (fStarMod K) ≤ c) (hcκ : c ≤ κ) :
    xt T K ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := by
  set R := pCoreOf 2 K with hR
  have hRT : R ≤ T := pCoreOf_le_of_sylow hT hTK
  set U : Subgroup V := Fx ρ (Wcl Ω c R) with hU
  have hKst : ∀ g ∈ K, g ∈ stabV ρ U := fun g hg =>
    mem_stabV_Fx_of_conj (conjSubgroup_Wcl_eq hΩ c (conjSubgroup_pCoreOf hg))
  set X := xt T K with hX
  have hXK : X ≤ K := xt_le hTK
  set Y : Subgroup G := X ⊓ cenV ρ U with hY
  have hYX : Y ≤ X := inf_le_left
  have hYn : ∀ g ∈ X, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    refine ⟨X.mul_mem (X.mul_mem hg (hYX hy)) (X.inv_mem hg), fun u hu => ?_⟩
    have hu' : ρ g⁻¹ u ∈ U := (hKst g⁻¹ (K.inv_mem (hXK hg)) u).2 hu
    have hy' : ρ y (ρ g⁻¹ u) = ρ g⁻¹ u := hy.2 _ hu'
    calc ρ (g * y * g⁻¹) u = ρ g (ρ y (ρ g⁻¹ u)) := by
          simp only [map_mul, MulAut.mul_apply]
      _ = ρ g (ρ g⁻¹ u) := by rw [hy']
      _ = u := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hD2 : ∀ d ∈ D, d ^ 2 = 1 := fun d hd => (hel A hA).1 d (hDA hd)
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => (hel A hA).2 a (hDA ha) b (hDA hb)
  have hm1 : mQuot D (D ⊓ R) ≤ CFSG.Open.pRank 2 (fStarMod K) :=
    mQuot_le_pRank_fStarMod hDX hD2 hDc
  have hm : mQuot A (D ⊓ R) ≤ c := by
    have := mQuot_add (inf_le_left : D ⊓ R ≤ D) hDA
    omega
  have hFW : D ⊓ R ≤ Wcl Ω c R := le_Wcl inf_le_right ⟨A, hA, inf_le_left.trans hDA, hm⟩
  have hFx : Fx ρ (D ⊓ R) = Fx ρ A := hfix A hA _ (inf_le_left.trans hDA) (hm.trans hcκ)
  have hUD : U ≤ Fx ρ D := (Fx_anti hFW).trans (hFx.le.trans (Fx_anti hDA))
  have hDY : D ≤ Y := fun d hd =>
    ⟨(le_sup_right : T ≤ X) (hDT hd), fun u hu => mem_Fx.1 (hUD hu) d hd⟩
  have hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 X) := fun h =>
    hDR ((le_inf hDY hDT).trans (h.trans (pCoreOf_xt_le hTK hF)))
  have hYc : Y ≤ cenV ρ (Fx ρ (Wcl Ω c T)) := fun y hy u hu =>
    hy.2 u (Fx_anti (Wcl_mono_base c hRT) hu)
  refine (xt_good hT hTK hF hYX hYn hYT).trans
    (sup_le (normalizer_le_stabV hΩ c) (sup_le ?_ (hYc.trans (cenV_le_stabV ρ _))))
  exact Subgroup.le_normalizer.trans (normalizer_le_stabV hΩ c)

open Classical in
theorem card_bad_le_of_split {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hF : CFSG.IsQuasisimple ↥(fStarMod H) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod H) = p)
    (hspl : H ≤ Subgroup.normalizer ((fStarPre H ⊔ T : Subgroup G) : Set G)) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ H ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank H := by
  refine (Finset.card_le_card ?_).trans
    (card_filter_bad_le (fun c => Wcl Ω c T ≤ pCoreOf 2 H) (iRank H) (κ + 1))
  intro c hc
  obtain ⟨hcr, hcH⟩ := Finset.mem_filter.1 hc
  have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
  refine Finset.mem_filter.2 ⟨hcr, fun hQ => hcH (le_stabV_of_le_pCore hΩ hT hTH hQ), ?_⟩
  intro j hj
  by_contra hjQ
  exact hcH (le_stabV_of_not_le hΩ hel hfix hT hTH hF hj hcκ hjQ 0 (Or.inl hspl) (by omega))

open Classical in
theorem card_bad_le_of_index_two {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    (hidx : (T ⊓ fStarPre K).relIndex T = 2)
    (hns : ¬ K ≤ Subgroup.normalizer ((fStarPre K ⊔ T : Subgroup G) : Set G)) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
        iRank K + 1 ∧
      (CFSG.Open.pRank 2 (fStarMod K) < iRank K →
        ((Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
          iRank K) := by
  set k := iRank K with hk
  set R := pCoreOf 2 K with hR
  set TX := T ⊓ fStarPre K with hTX
  set X := xt T K with hX
  set B := bk T K with hB
  have hRTX : R ≤ TX := le_inf (pCoreOf_le_of_sylow hT hTK) (pCoreOf_le_fStarPre K)
  have hTXX : T ≤ X := le_sup_right
  have hTB : T ≤ B := le_bk hTK
  have hrX : ∀ D : Subgroup G, D ≤ X → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 X) ≤ k :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (xt_rank hT hTK hF)
  have hrB : ∀ D : Subgroup G, D ≤ B → (∀ b ∈ D, b ^ 2 = 1) →
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → mQuot D (D ⊓ pCoreOf 2 B) ≤ 1 :=
    fun D hD hD2 hDc => (mQuot_inf_pCoreOf_le hD hD2 hDc).trans (bk_rank hT hTK hidx)
  have hgX : ∀ Y : Subgroup G, Y ≤ X → (∀ h ∈ X, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 X) → X ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
    fun Y hY hYn hYT => xt_good hT hTK hF hY hYn hYT
  have hgB : ∀ Y : Subgroup G, Y ≤ B → (∀ h ∈ B, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) →
      ¬ (Y ⊓ T ≤ pCoreOf 2 B) → B ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) :=
    fun Y hY hYn hYT => bk_good hT hTK hidx hY hYn hYT
  have hXR : pCoreOf 2 X ≤ R := pCoreOf_xt_le hTK hF
  have hSB' : TX ≤ pCoreOf 2 B := inf_le_pCoreOf_bk hT hTK
  have hBS : pCoreOf 2 B ≤ TX := pCoreOf_bk_le hT hTK hidx hns
  have hKXB : ∀ c, X ≤ stabV ρ (Fx ρ (Wcl Ω c T)) → B ≤ stabV ρ (Fx ρ (Wcl Ω c T)) →
      K ≤ stabV ρ (Fx ρ (Wcl Ω c T)) := fun c hXc hBc =>
    (le_sup_bk hT hTK).trans (sup_le (le_sup_left.trans hXc) hBc)
  set Q : ℕ → Prop := fun c => Wcl Ω c T ≤ R with hQ
  set P : ℕ → Prop := fun c => Wcl Ω c T ≤ TX with hP
  set SX := (Finset.range (κ + 1)).filter (fun c => ¬ Q c ∧ ∀ j, j + k ≤ c → Q j) with hSX
  set SB := (Finset.range (κ + 1)).filter (fun c => ¬ P c ∧ ∀ j, j + 1 ≤ c → P j) with hSBd
  set bad := (Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))
    with hbad
  have hsub : bad ⊆ SX ∪ SB := by
    intro c hc
    obtain ⟨hcr, hcK⟩ := Finset.mem_filter.1 hc
    have hcκ : c ≤ κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hcr)
    by_contra hn
    rw [Finset.mem_union, not_or] at hn
    apply hcK
    by_cases hQc : Q c
    · exact le_stabV_of_le_pCore hΩ hT hTK hQc
    refine hKXB c ?_ ?_
    · have hex : ¬ ∀ j, j + k ≤ c → Q j := fun h => hn.1 (Finset.mem_filter.2 ⟨hcr, hQc, h⟩)
      push Not at hex
      obtain ⟨j, hj, hjQ⟩ := hex
      exact le_stabV_of_good hΩ hel hfix hT hTXX hrX hgX hj hcκ (fun h => hjQ (h.trans hXR))
    · by_cases hPc : P c
      · exact le_stabV_of_le_pCore hΩ hT hTB (hPc.trans hSB')
      have hex : ¬ ∀ j, j + 1 ≤ c → P j := fun h => hn.2 (Finset.mem_filter.2 ⟨hcr, hPc, h⟩)
      push Not at hex
      obtain ⟨j, hj, hjP⟩ := hex
      exact le_stabV_of_good hΩ hel hfix hT hTB hrB hgB hj hcκ (fun h => hjP (h.trans hBS))
  have hcX : SX.card ≤ k := card_filter_bad_le _ _ _
  have hcB : SB.card ≤ 1 := card_filter_bad_le _ _ _
  have hu : (SX ∪ SB).card ≤ SX.card + SB.card := Finset.card_union_le _ _
  refine ⟨(Finset.card_le_card hsub).trans (by omega), fun hrk => ?_⟩
  by_cases hle : (SX ∪ SB).card ≤ k
  · exact (Finset.card_le_card hsub).trans hle
  push Not at hle
  have hk1 : 1 ≤ k := by omega
  have hSXk : SX.card = k := by omega
  have hSB1 : SB.card = 1 := by omega
  have hinter : (SX ∩ SB).card = 0 := by
    have := Finset.card_union_add_card_inter SX SB
    omega
  obtain ⟨b, hbe⟩ := Finset.card_eq_one.1 hSB1
  have hbSB : b ∈ SB := by rw [hbe]; exact Finset.mem_singleton_self b
  obtain ⟨hbr, hbP, hbP'⟩ := Finset.mem_filter.1 hbSB
  have hbSX : b ∉ SX := fun h => by
    have : b ∈ SX ∩ SB := Finset.mem_inter.2 ⟨h, hbSB⟩
    rw [Finset.card_eq_zero.1 hinter] at this
    exact Finset.notMem_empty b this
  have hne : SX.Nonempty := Finset.card_pos.1 (by omega)
  set a := SX.min' hne with ha
  have haSX : a ∈ SX := SX.min'_mem hne
  obtain ⟨har, haQ, -⟩ := Finset.mem_filter.1 haSX
  have hIco : SX ⊆ Finset.Ico a (a + k) := by
    intro c hc
    rw [Finset.mem_Ico]
    refine ⟨SX.min'_le c hc, ?_⟩
    by_contra hlt
    push Not at hlt
    exact haQ ((Finset.mem_filter.1 hc).2.2 _ hlt)
  have hSXeq : SX = Finset.Ico a (a + k) :=
    Finset.eq_of_subset_of_card_le hIco (by rw [Nat.card_Ico, hSXk]; omega)
  have hQP : ∀ c, Q c → P c := fun c h => h.trans hRTX
  have hba : a ≤ b := by
    by_contra hlt
    push Not at hlt
    have hexQ : ∃ c, ¬ Q c := ⟨b, fun h => hbP (hQP b h)⟩
    set m := Nat.find hexQ with hm
    have hmb : m ≤ b := Nat.find_min' hexQ (fun h => hbP (hQP b h))
    have hmSX : m ∈ SX := by
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_le_of_lt hmb (Finset.mem_range.1 hbr)),
        Nat.find_spec hexQ, fun j hj => ?_⟩
      by_contra hjQ
      exact Nat.find_min hexQ (by omega : j < m) hjQ
    have := SX.min'_le m hmSX
    omega
  have hbk : a + k ≤ b := by
    by_contra hlt
    push Not at hlt
    exact hbSX (hSXeq ▸ Finset.mem_Ico.2 ⟨hba, hlt⟩)
  set c₀ := a + CFSG.Open.pRank 2 (fStarMod K) with hc₀
  have hc₀SX : c₀ ∈ SX := hSXeq ▸ Finset.mem_Ico.2 ⟨by omega, by omega⟩
  have hc₀κ : c₀ ≤ κ :=
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hc₀SX).1)
  have hPa : P a := hbP' a (by omega)
  have hPc₀ : P c₀ := hbP' c₀ (by omega)
  obtain ⟨D, ⟨hDT, A, hA, hDA, hmA⟩, hDR⟩ : ∃ D ∈ {D | D ≤ T ∧ D ∈ Wset Ω a}, ¬ D ≤ R := by
    by_contra h
    push Not at h
    exact haQ (sSup_le h)
  have hDW : D ≤ Wcl Ω a T := le_Wcl hDT ⟨A, hA, hDA, hmA⟩
  have hDX : D ≤ fStarPre K := (hDW.trans hPa).trans inf_le_right
  have hKc₀ : K ≤ stabV ρ (Fx ρ (Wcl Ω c₀ T)) :=
    hKXB c₀ (xt_le_stabV_of_mem hΩ hel hfix hT hTK hF hA hDA hDT hDX hDR hmA le_rfl hc₀κ)
      (le_stabV_of_le_pCore hΩ hT hTB (hPc₀.trans hSB'))
  have hsub' : bad ⊆ (SX ∪ SB).erase c₀ := by
    intro c hc
    refine Finset.mem_erase.2 ⟨fun h => ?_, hsub hc⟩
    rw [h] at hc
    exact (Finset.mem_filter.1 hc).2 hKc₀
  have h1 := Finset.card_le_card hsub'
  rw [Finset.card_erase_of_mem (Finset.mem_union_left _ hc₀SX)] at h1
  omega

open Classical in
theorem card_bad_le_of_rank {V : Type} [CommGroup V] {ρ : G →* MulAut V} {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : ∀ A ∈ Ω, ∀ g : G, conjSubgroup A g ∈ Ω)
    (hel : ∀ A ∈ Ω, (∀ a ∈ A, a ^ 2 = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {κ : ℕ}
    (hfix : ∀ A ∈ Ω, ∀ B : Subgroup G, B ≤ A → mQuot A B ≤ κ → Fx ρ B = Fx ρ A)
    {K : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    (hidx : (T ⊓ fStarPre K).relIndex T = 2)
    (hns : ¬ K ≤ Subgroup.normalizer ((fStarPre K ⊔ T : Subgroup G) : Set G))
    (hrk : CFSG.Open.pRank 2 (fStarMod K) < iRank K) :
    ((Finset.range (κ + 1)).filter (fun c => ¬ K ≤ stabV ρ (Fx ρ (Wcl Ω c T)))).card ≤
      iRank K :=
  (card_bad_le_of_index_two hΩ hel hfix hT hTK hF hidx hns).2 hrk

end CFSG.Quasithin.RonanE42.Gen
