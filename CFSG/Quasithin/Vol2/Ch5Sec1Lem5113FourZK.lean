module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourNat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113A7Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FactA7FF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K Q W : Subgroup G), ⁅K, K⁆ = K →
    Nonempty (O2Q K ≃* alternatingGroup (Fin 7)) →
    IsSylowTwoOf Q (K ⊔ Q) → Q ≤ Subgroup.normalizer (K : Set G) → SQTKGroup ↥(K ⊔ Q) →
    IsTwoReducedIn (K ⊔ Q) W → ¬ K ≤ Subgroup.centralizer (W : Set G) →
    ¬ thompsonJ Q ≤ Subgroup.centralizer (W : Set G) →
      ⁅W, K⁆ ⊔ (W ⊓ Subgroup.centralizer (K : Set G)) = W ∧
        ⁅W, K⁆ ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∧
        (∀ J : Subgroup G, J ≤ ⁅W, K⁆ → K ≤ Subgroup.normalizer (J : Set G) →
          J = ⊥ ∨ J = ⁅W, K⁆) ∧
        (Nat.card ↥⁅W, K⁆ = 2 ^ 4 ∨ Nat.card ↥⁅W, K⁆ = 2 ^ 6)

theorem stmt5_1_13_four_ZK_of (h5171 : A5.Stmt5_1_7_one) (hFF : FactA7FF) :
    Stmt5_1_13_four_ZK := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hKZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨e⟩ := hA
  have hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)) := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  obtain ⟨hW, hKhW, hJWc⟩ := m.commutator_thompsonJ_ne_bot h5171 hmax hs hZ
  have hKhperf : ⁅conjClosure Kh₁ T, conjClosure Kh₁ T⁆ = conjClosure Kh₁ T :=
    A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1)
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    le_normalizer_conjClosure Kh₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) := fun hle => hJWc (by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle)
  obtain ⟨-, hCU, hirr, hcardU⟩ := hFF G (conjClosure Kh₁ T) T _ hKhperf ⟨e⟩ hTY hTKh
    (InternalSec.sqtkGroup_of_localSQTK hloc hmax.1.2.2.2) hW hKhW hJW
  have hWT : conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) ≤ T :=
    (MinParabolic.le_pCoreOf_of_isTwoReduced hW).trans (F7.isSylowTwoOf_pCoreOf_le hTY)
  have hYW := hW.2.1
  have hUW := A7ZK.commutator_le_left_of_le_normalizer (le_sup_left.trans hYW)
  have hKhU := A7ZK.le_normalizer_commutator (le_sup_left.trans hYW)
    (Subgroup.le_normalizer : conjClosure Kh₁ T ≤ _)
  have hTU := A7ZK.le_normalizer_commutator (le_sup_right.trans hYW) hTKh
  have hUel := A7ZK.isElemAbelian_of_le hUW hW.2.2.1
  have hU1 : ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardU
    norm_num at hcardU
  have hKhUc : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer
      ((⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
        conjClosure Kh₁ T⁆ : Subgroup G) : Set G) := by
    intro hle
    apply hU1
    rw [eq_bot_iff, ← hCU]
    exact le_inf le_rfl (Subgroup.le_centralizer_iff.mp hle)
  have hOW : pCoreOf 2 (conjClosure Kh₁ T) ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) := by
    refine hW.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (hTKh.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure Kh₁ T) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  have hOU : pCoreOf 2 (conjClosure Kh₁ T) ≤ Subgroup.centralizer
      ((⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
        conjClosure Kh₁ T⁆ : Subgroup G) : Set G) :=
    hOW.trans (Subgroup.centralizer_le fun x hx => hUW hx)
  have hKKh : oTwoUpper H ≤ conjClosure Kh₁ T := m.lt.le
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have h60 : Nat.card (O2Q (oTwoUpper H)) = 60 :=
    (card_of_lieModel_L2 (n := 2) (by norm_num) hc5.1).trans (by norm_num)
  have hcK : Nat.card (oTwoUpper H) = 60 * Nat.card (CFSG.pCore 2 ↥(oTwoUpper H)) := by
    rw [← h60]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(oTwoUpper H)))
  have hKb : Nat.card (oTwoUpper H) =
      Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) * Nat.card (barMap hKKh).ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (barMap hKKh).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (barMap_surjective hKKh)).toEquiv] at h1
    exact h1
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (isPGroup_ker_barMap hKKh)
  have hnum : Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) * 2 ^ b = 60 * 2 ^ a := by
    rw [← hb, ← ha, ← hcK, hKb]
  have h15 : 15 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) := by
    have h1 : 15 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) * 2 ^ b :=
      hnum ▸ Dvd.dvd.mul_right (by norm_num) _
    exact (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 15 2)).dvd_of_dvd_mul_right h1
  have h7 : ¬ 7 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) := fun hd => by
    have h1 : 7 ∣ 60 * 2 ^ a := hnum ▸ Dvd.dvd.mul_right hd _
    have h2 := (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 7 2)).dvd_of_dvd_mul_right h1
    norm_num at h2
  have h9 : ¬ 9 ∣ Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) := fun hd => by
    have h1 : 9 ∣ 60 * 2 ^ a := hnum ▸ Dvd.dvd.mul_right hd _
    have h2 := (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h1
    norm_num at h2
  have h5K : 5 ∣ Nat.card (oTwoUpper H) := hcK ▸ Dvd.dvd.mul_right (by norm_num) _
  have hcR : Nat.card ((modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom) =
      Nat.card (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) :=
    Subgroup.card_map_of_injective e.injective
  have hRperf : ⁅(modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom,
      (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom⁆ =
        (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom := by
    have : Group.IsPerfect ↥(oTwoUpper H) := Subgroup.isPerfect_iff.mpr hKperf
    have : Group.IsPerfect ↥(modO2Image (conjClosure Kh₁ T) (oTwoUpper H)) :=
      Group.IsPerfect.ofSurjective (barMap_surjective hKKh)
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp this]
  have hTsyl : IsSylowTwoOf (T ⊓ conjClosure Kh₁ T) (conjClosure Kh₁ T) :=
    A4.isSylowTwoOf_inf_normal hTY le_sup_left (sup_le Subgroup.le_normalizer hTKh)
  have hS : IsSylowTwoOf ((modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)).map
      e.toMonoidHom) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_map_of_surjective
      (isSylowTwoOf_top_subgroupOf hTsyl) _ (QuotientGroup.mk'_surjective _)) _ e.surjective
  have hSR : (modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)).map e.toMonoidHom ≤
      Subgroup.normalizer (((modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) :=
    (Subgroup.map_mono (Vol2.Ch11.SecS.modO2Image_le_normalizer (inf_le_left.trans hTK))).trans
      (Subgroup.le_normalizer_map _)
  obtain ⟨g, hg⟩ := A7Std.exists_conj_eq_r0 hRperf (hcR ▸ h15) (hcR ▸ h7) (hcR ▸ h9) hS hSR
  have hR' : (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map
      (e.trans (MulAut.conj g)).toMonoidHom = A7Std.r0 := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hUKU := A7ZK.commutator_le_left_of_le_normalizer (hKKh.trans hKhU)
  have hKey : ⁅⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆, oTwoUpper H⁆ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
    rcases hcardU with h16 | h64
    · refine eq_bot_iff.mpr ((inf_le_inf_right _ hUKU).trans ?_)
      exact (A7ZK.inf_centralizer_eq_bot_of_card_sixteen hKhperf hs hKhU hKhUc hKKh h5K
        (by rw [h16]; norm_num)).le
    · obtain ⟨β, hβ⟩ := A7ZK.exists_coreMod_equiv (e.trans (MulAut.conj g)) hKhU hUel hOU hirr
        hKhUc h64
      exact A7ZK.commutator_inf_centralizer_eq_bot _ hKhU hKKh β hβ hR'
  obtain ⟨x, hxK, -, hxU⟩ :=
    A7ZK.exists_pow_five_not_mem_centralizer hKhperf hs hKhU hKhUc hKKh h5K
  have hUK1 : ⁅⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆, oTwoUpper H⁆ ≠ ⊥ := by
    intro hbot
    apply hxU
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hxK
  have hUKT := hUKU.trans (hUW.trans hWT)
  have hTUK := A7ZK.le_normalizer_commutator hTU hTK
  apply inf_centralizer_ne_bot_of_normalizes h.sylow.1 hUKT hTUK hUK1
  rw [eq_bot_iff, ← hKey]
  intro y hy
  have hyU := (Subgroup.mem_inf.mp hy).1
  have hyZ : y ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUKT hyU, (Subgroup.mem_inf.mp hy).2,
      hUel.2 y (hUKU hyU)⟩
  exact Subgroup.mem_inf.mpr ⟨hyU, Subgroup.mem_centralizer_iff.mpr fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hKZ hk) y hyZ).symm⟩

end CFSG.Quasithin.H13
