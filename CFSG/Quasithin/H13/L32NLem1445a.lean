module

public import CFSG.Quasithin.H13.L32NLem1444o

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup4

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem pow_four_of_cent [IsMulCommutative ↥V] (S' : L32NSet14.Setting G T L V V₂) {x : G}
    (hxL : x ∈ L) (hx : ∀ v ∈ V₂, x * v * x⁻¹ = v) : x ^ 4 = 1 := by
  obtain ⟨z, a, b, -, -, -, -, hb, hbV⟩ := S'.exists_basis
  have hxN := S.L_le_normV hxL
  have hxb : x * b * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN b).mp hb
  have hxbV : x * b * x⁻¹ ∉ V₂ := fun h => hbV (by
    have hw := hx _ h
    have h1 : x⁻¹ * (x * b * x⁻¹) * x = x * b * x⁻¹ := by
      calc x⁻¹ * (x * b * x⁻¹) * x = x⁻¹ * (x * (x * b * x⁻¹) * x⁻¹) * x := by rw [hw]
        _ = x * b * x⁻¹ := by group
    rw [show b = x⁻¹ * (x * b * x⁻¹) * x by group, h1]
    exact h)
  have hv₂ : b * (x * b * x⁻¹) ∈ V₂ := (S'.mem_V hb hbV hxb).resolve_left hxbV
  set v₂ := b * (x * b * x⁻¹) with hv₂def
  have hb2 : b * b = 1 := S'.mul_self_V hb
  have hxbe : x * b * x⁻¹ = b * v₂ := by
    rw [hv₂def, ← mul_assoc, hb2, one_mul]
  have hx2b : x ^ 2 * b * (x ^ 2)⁻¹ = b := by
    have hv₂V : v₂ ∈ V := S.plane.1.1 hv₂
    calc x ^ 2 * b * (x ^ 2)⁻¹ = x * (x * b * x⁻¹) * x⁻¹ := by rw [pow_two]; group
      _ = x * (b * v₂) * x⁻¹ := by rw [hxbe]
      _ = (x * b * x⁻¹) * (x * v₂ * x⁻¹) := by group
      _ = b * v₂ * v₂ := by rw [hxbe, hx v₂ hv₂]
      _ = b := by rw [mul_assoc, S'.mul_self_V hv₂V, mul_one]
  have hx2V : ∀ v ∈ V, x ^ 2 * v * (x ^ 2)⁻¹ = v := by
    intro v hv
    have hV₂ : ∀ w ∈ V₂, x ^ 2 * w * (x ^ 2)⁻¹ = w := fun w hw => by
      calc x ^ 2 * w * (x ^ 2)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = w := by rw [hx w hw, hx w hw]
    rcases S'.mem_V hb hbV hv with h | h
    · exact hV₂ v h
    · calc x ^ 2 * v * (x ^ 2)⁻¹ = (x ^ 2 * b * (x ^ 2)⁻¹)⁻¹ * (x ^ 2 * (b * v) * (x ^ 2)⁻¹) := by
            group
        _ = v := by rw [hx2b, hV₂ _ h]; group
  have hx2 : x ^ 2 ∈ V := S.centL.le ⟨L.pow_mem hxL 2,
    Subgroup.mem_centralizer_iff.mpr fun v hv => by
      calc v * x ^ 2 = x ^ 2 * v * (x ^ 2)⁻¹ * x ^ 2 := by rw [hx2V v hv]
        _ = x ^ 2 * v := by group⟩
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact S.elem.2 _ hx2

theorem Wg_le_T [IsMulCommutative ↥V] (hT : quasithinIsSylowTwo T)
    (S' : L32NSet14.Setting G T L V V₂) :
    CFSG.conjugate (l32nW T V V₂) g ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₂ := L ⊓ Subgroup.centralizer (V₂ : Set G) with hC₂
  have hC₂2 : IsPGroup 2 C₂ := fun x => ⟨2, Subtype.ext (by
    have := S.pow_four_of_cent S' x.2.1 fun v hv => by
      rw [← (Subgroup.mem_centralizer_iff.mp x.2.2 v hv)]
      group
    simpa using this)⟩
  have hTC : T ≤ Subgroup.normalizer (C₂ : Set G) := fun t ht => by
    have htL := S.TL ht
    have htV₂ := S.plane.1.2.2 ht
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp htL x).mp hx.1
    · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hv' : t⁻¹ * v * t ∈ V₂ := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem htV₂) v).mp hv
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
      calc v * (t * x * t⁻¹) = t * ((t⁻¹ * v * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * v * t)) * t⁻¹ := by rw [h1]
        _ = t * x * t⁻¹ * v := by group
  obtain ⟨P, hP⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hT
  have hsup : IsPGroup 2 ↥(T ⊔ C₂) :=
    IsPGroup.to_sup_of_normal_right' (hP ▸ P.isPGroup') hC₂2 hTC
  have hmax : T ⊔ C₂ = T := by
    have := P.is_maximal' hsup (by rw [hP]; exact le_sup_left)
    rwa [hP] at this
  intro x hx
  rw [← hmax]
  exact Subgroup.mem_sup_right ⟨S.Wg_le_L hx, Wg_le_cent S.g_normV₂ hx⟩

theorem eq_UWg_of_le [IsMulCommutative ↥V] (hT : quasithinIsSylowTwo T)
    (S' : L32NSet14.Setting G T L V V₂)
    (hTL : T ≤ L) : T = fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g ≤ T :=
    sup_le (S.U_le_Q.trans S.QT) (S.Wg_le_T hT S')
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [S.card_UWg]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT.1
  have hdvd : Nat.card T ∣ Nat.card L := Subgroup.card_dvd_of_le hTL
  rw [S.cardL, hk, show (1344 : ℕ) = 2 ^ 6 * 21 by norm_num] at hdvd
  have h2 : 2 ^ k ∣ 2 ^ 6 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h2

end Setup4

end L1444

open L1444 in
theorem lemma1445Three_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest) (h14451 : Lemma1445One) : Lemma1445Three := by
  intro G _ _ T L V h hext h32 hG2 V₂ g hV₂ hgP hgH
  obtain ⟨D, Q₁, Q₂, S⟩ :=
    exists_setup4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2 hV₂ hgP hgH
  obtain ⟨_, S'⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
  have hTL : T ≤ L := by
    have hTN := S.TL
    rwa [h14451 G T L V h hext h32 hG2] at hTN
  exact S.eq_UWg_of_le h.hyp.h13.sylow S' hTL

open L1444 in
theorem lemma1445Two_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest) (hCTL : Lemma1444CTL)
    (h14453 : Lemma1445Three) : Lemma1445Two := by
  intro G _ _ T L V h hext h32 hG2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUQ := fsuU_eq_pCoreOf_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL G T L V
    h hext h32 hG2
  refine ⟨hUQ, ?_⟩
  obtain ⟨hKel, hK9⟩ :=
    lemma1444One_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  obtain ⟨hHKT, -⟩ :=
    lemma1444Seven_of_inputs h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  obtain ⟨D, Q₁, Q₂, S⟩ :=
    exists_setup4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2 hV₂ hgP hgH
  have hT64 : Nat.card T = 64 :=
    (congrArg (fun X : Subgroup G => Nat.card ↥X)
      (h14453 G T L V h hext h32 hG2 V₂ g hV₂ hgP hgH)).trans S.card_UWg
  set H := l32nH T V with hHdef
  set K := oTwoUpper H with hKdef
  have hKH : K ≤ H := oTwoUpper_le H
  have hTS := h.isSylowTwoOf_l32nH hV
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTS
  refine ⟨imageOTwoQuot H K, ?_, hKel, hK9, ?_⟩
  ·
    have hKn : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper H)
    exact hKn.map _ (QuotientGroup.mk'_surjective _)
  have hTK : T ⊓ K = K ⊓ pCoreOf 2 H := by
    apply le_antisymm
    · rintro x ⟨hxT, hxK⟩
      refine ⟨hxK, ?_⟩
      have hxH : x ∈ H := hKH hxK
      set y : OTwoQuot H := QuotientGroup.mk ⟨x, hxH⟩ with hy
      have hyK : y ∈ imageOTwoQuot H K := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
      have hy3 : y ^ 3 = 1 := hKel.2 y hyK
      obtain ⟨k, hk⟩ := hTS.2.1 ⟨x, hxT⟩
      have hx2 : x ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hy2 : y ^ 2 ^ k = 1 := by
        rw [hy, ← QuotientGroup.mk_pow]
        have : (⟨x, hxH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hx2)
        rw [this, QuotientGroup.mk_one]
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      have hy1 : y = 1 := by
        have h1 : y ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hy3, hy2⟩
        rwa [hcop, pow_one] at h1
      rw [hy, QuotientGroup.eq_one_iff] at hy1
      exact ⟨_, hy1, rfl⟩
    · exact fun x hx => ⟨hQT hx.2, hx.1⟩
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hTS.1.trans (le_normalizer_oTwoUpper H)
  have hprod := L32NSet14.card_sup_mul_card_inf hTN
  have hsup : T ⊔ K = H := by rw [sup_comm, ← hHKT]
  rw [hsup, hTK, hT64] at hprod
  have hKcard := card_eq_card_imageOTwoQuot_mul H K hKH
  rw [hK9] at hKcard
  have hpos : 0 < Nat.card ↥(K ⊓ pCoreOf 2 H) := Nat.card_pos
  have hH : Nat.card H = 576 := by
    rw [hKcard] at hprod
    have : Nat.card H * Nat.card ↥(K ⊓ pCoreOf 2 H) = 576 * Nat.card ↥(K ⊓ pCoreOf 2 H) := by
      rw [hprod]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hQ : Nat.card ↥(CFSG.Open.pCore 2 ↥H) = 32 := by
    have h1 : Nat.card ↥(pCoreOf 2 H) = Nat.card ↥(CFSG.Open.pCore 2 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h1, ← hUQ, h32]
    norm_num
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
  rw [hH, hQ] at hquot
  have hidx := Subgroup.card_mul_index (imageOTwoQuot H K)
  rw [hK9] at hidx
  have h18 : Nat.card (OTwoQuot H) = 18 := by
    have : Nat.card (↥H ⧸ CFSG.Open.pCore 2 ↥H) = 18 := by omega
    exact this
  rw [h18] at hidx
  omega

end CFSG.Quasithin.H13
