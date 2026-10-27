module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inn
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem22

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_relIndex_two_pow {Y Z O : Subgroup G} (hZY : Z ≤ Y)
    (hO : IsPGroup 2 O) (hOY : O ≤ Y) (hYO : Y ≤ Subgroup.normalizer (O : Set G))
    (hYZ : ∃ a : ℕ, Z.relIndex Y = 2 ^ a)
    (hc : ∀ z ∈ Z, ∀ y ∈ Y, y * z * y⁻¹ * z⁻¹ ∈ O) {y₀ : G} (hy₀ : y₀ ∈ Y)
    (h2 : ∃ m : ℕ, y₀ ^ (2 ^ m) = 1) : y₀ ∈ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h2
  have hz : IsPGroup 2 (Subgroup.zpowers y₀) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨m, Subtype.ext ?_⟩
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]
  obtain ⟨P, hP, hyP⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr hy₀) hz
  have hOn : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYO
  have hOP : O ≤ P := A4.le_of_normal_of_isSylowTwoOf hP hOY hOn hO
  have hZP : Z ≤ Subgroup.normalizer (P : Set G) := by
    intro z hz'
    refine mem_normalizer_of_forall_conj_mem_of_le fun p hp => ?_
    have h1 : p * z * p⁻¹ * z⁻¹ ∈ O := hc z hz' p (hP.1 hp)
    have e : z * p * z⁻¹ = (p * z * p⁻¹ * z⁻¹)⁻¹ * p := by group
    rw [e]
    exact P.mul_mem (hOP (O.inv_mem h1)) hp
  have hW : Z ⊔ P = Y := by
    have hWY : Z ⊔ P ≤ Y := sup_le hZY hP.1
    obtain ⟨a, ha⟩ := hYZ
    have hd1 : (Z ⊔ P).relIndex Y ∣ 2 ^ a := by
      rw [← ha]
      exact Subgroup.relIndex_dvd_of_le_left Y le_sup_left
    have hd2 : (Z ⊔ P).relIndex Y ∣ P.relIndex Y :=
      Subgroup.relIndex_dvd_of_le_left Y le_sup_right
    have hodd : ¬ 2 ∣ P.relIndex Y := hP.2.2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    have hj0 : j = 0 := by
      by_contra hj0
      apply hodd
      exact (dvd_pow_self 2 hj0).trans (hj ▸ hd2)
    rw [hj0, pow_zero] at hj
    exact le_antisymm hWY (Subgroup.relIndex_eq_one.mp hj)
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := hW ▸ sup_le hZP Subgroup.le_normalizer
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP.1 hYP hP.2.1
    (hyP (Subgroup.mem_zpowers y₀))

theorem le_normalizer_of_sq_mem {I N : Subgroup G} (hNI : N ≤ I)
    (hsq : ∀ x ∈ I, x * x ∈ N) : I ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
  have e : g * x * g⁻¹ = (g * x) * (g * x) * x⁻¹ * (g⁻¹ * g⁻¹) := by group
  rw [e]
  exact N.mul_mem (N.mul_mem (hsq _ (I.mul_mem hg (hNI hx))) (N.inv_mem hx))
    (hsq _ (I.inv_mem hg))

theorem map_conj_sq_eq_of_ncard_two {X : Set (Subgroup G)} (hX : X.ncard = 2)
    {K : Subgroup G} (hKX : K ∈ X) {g : G}
    (hg : ∀ Y ∈ X, Y.map (MulAut.conj g).toMonoidHom ∈ X) :
    K.map (MulAut.conj (g * g)).toMonoidHom = K := by
  set f : Subgroup G → Subgroup G := fun Y => Y.map (MulAut.conj g).toMonoidHom with hf
  have hinj : Function.Injective f := fun A B hAB =>
    Subgroup.map_injective (MulAut.conj g).injective hAB
  rw [map_conj_mul_ch625]
  change f (f K) = K
  by_cases hne : f K = K
  · rw [hne, hne]
  have hfK : f K ∈ X := hg K hKX
  have hffK : f (f K) ∈ X := hg _ hfK
  have hX2 : ∀ Y ∈ X, Y = K ∨ Y = f K := by
    intro Y hY
    by_contra hY'
    push Not at hY'
    have h3 : ({K, f K, Y} : Set (Subgroup G)) ⊆ X := by
      intro Z hZ
      rcases hZ with rfl | rfl | rfl
      · exact hKX
      · exact hfK
      · exact hY
    have h4 := Set.ncard_le_ncard h3 (Set.toFinite X)
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h0 => hne h0.symm, fun h0 => hY'.1 h0.symm⟩),
      Set.ncard_pair (fun h0 => hY'.2 h0.symm)] at h4
    omega
  rcases hX2 _ hffK with h1 | h1
  · exact h1
  · exact absurd (hinj h1) hne

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

theorem pCoreOf_I_ne_bot :
    pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) ≠ ⊥ := by
  intro h0
  apply d.hyp.toHyp611Nat.ZS_ne_bot
  rw [eq_bot_iff, ← h0]
  have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
    B2F.isElemAbelian_mono inf_le_left d.hyp.toHyp611.isElemAbelian
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
    (Subgroup.centralizer_le_normalizer _) (B2F.isPGroup_of_isElemAbelian hZel)
  intro z hz
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => B2F.isElemAbelian_comm hZel hx hz

include hI in
theorem I_le_normalizer_NIK :
    Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (ch6ZS T L V : Set G) ⊓
        Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) := by
  have : IsSimpleGroup G := d.hyp.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat d.hyp.nonabelian d.hyp.qtke).1
  set I := Subgroup.centralizer (ch6ZS T L V : Set G) with hIdef
  rcases Vol2Native.lemma_1_2_1_three hLoc hI.h37 hI.h38 d.pCoreOf_I_ne_bot d.comp with hn | ⟨h2, -⟩
  · have hIK : I ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp d.comp)).mp hn
    rw [inf_eq_left.mpr hIK]
    exact Subgroup.le_normalizer
  · refine le_normalizer_of_sq_mem inf_le_left fun x hx => ⟨I.mul_mem hx hx, ?_⟩
    have hperm : ∀ Y ∈ conjSubgroupsBy I K, Y.map (MulAut.conj x).toMonoidHom ∈
        conjSubgroupsBy I K := by
      rintro Y ⟨t, ht, rfl⟩
      exact ⟨x * t, I.mul_mem hx ht, (map_conj_mul_ch625 K x t).symm⟩
    have hKX : K ∈ conjSubgroupsBy I K := ⟨1, I.one_mem, by ext y; simp⟩
    exact mem_normalizer_of_map_conj_eq_ch625 (map_conj_sq_eq_of_ncard_two h2 hKX hperm)

include hI in
theorem isSylowTwoOf_S1 :
    IsSylowTwoOf (ch6S T L V ⊓ Subgroup.normalizer (K : Set G))
      (Subgroup.centralizer (ch6ZS T L V : Set G) ⊓ Subgroup.normalizer (K : Set G)) := by
  have hS := (stmt6_1_9 hI.h432 G T M L V n d.hyp.toHyp611Nat).1.2
  have h1 := A4.isSylowTwoOf_inf_normal hS inf_le_left (d.I_le_normalizer_NIK hI)
  have e : ch6S T L V ⊓ (Subgroup.centralizer (ch6ZS T L V : Set G) ⊓
      Subgroup.normalizer (K : Set G)) = ch6S T L V ⊓ Subgroup.normalizer (K : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr (inf_le_right : ch6S T L V ≤ _)]
  rwa [e] at h1

include hI in
theorem borel_le_M (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) :
    K ⊓ Subgroup.normalizer ((ch6S T L V ⊓ K : Subgroup G) : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := Subgroup.centralizer (ch6ZS T L V : Set G) with hIdef
  set S := ch6S T L V with hSdef
  set SK := S ⊓ K with hSK
  set B := K ⊓ Subgroup.normalizer (SK : Set G) with hB
  set R := ch6R T L V l with hRdef
  set OI := pCoreOf 2 I with hOI
  set W := R ⊔ OI with hW
  set X₀ := B ⊔ W with hX₀
  set OK := pCoreOf 2 K with hOK
  set Y := centralizerMod OK X₀ K with hY
  set C := SK ⊔ pCoreOf 2 Y with hC
  have hS2 : IsPGroup 2 S := d.hyp.sylow.1.to_le inf_le_left
  have hRS : R ≤ S := d.hyp.R_le_S hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not
  have hRI : R ≤ I := d.hyp.R_le_I hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not
  have hOIS : OI ≤ S := by
    have hS := (stmt6_1_9 hI.h432 G T M L V n d.hyp.toHyp611Nat).1.2
    exact F7.isSylowTwoOf_pCoreOf_le hS
  have hWS : W ≤ S := sup_le hRS hOIS
  have hRNK := d.R_le_NK hI
  have hOINK := d.O2_le_NK
  have hKI := d.K_le_I
  have hSKN : ∀ x ∈ S, x ∈ Subgroup.normalizer (K : Set G) →
      x ∈ Subgroup.normalizer (SK : Set G) := fun x hxS hxK =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hxS, hxK⟩
  have hBNK : B ≤ Subgroup.normalizer (K : Set G) := fun x hx => Subgroup.le_normalizer hx.1
  have hWNK : W ≤ Subgroup.normalizer (K : Set G) := sup_le hRNK hOINK
  have hX₀NK : X₀ ≤ Subgroup.normalizer (K : Set G) := sup_le hBNK hWNK
  have hX₀I : X₀ ≤ I := sup_le (fun x hx => hKI hx.1) (sup_le hRI
    (CFSG.LieType.BorelTits.pCoreOf_le 2 I))
  have hX₀SK : X₀ ≤ Subgroup.normalizer (SK : Set G) :=
    sup_le (fun x hx => hx.2) fun x hx => hSKN x (hWS hx) (hWNK hx)
  have hSKB : SK ≤ B := le_inf inf_le_right Subgroup.le_normalizer
  have hX₀OK : X₀ ≤ Subgroup.normalizer (OK : Set G) :=
    hX₀NK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hYX₀ : Y ≤ X₀ := centralizerMod_le_left _ _ _
  have hX₀Y : X₀ ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_centralizerMod hX₀OK Subgroup.le_normalizer hX₀NK
  have hOKS : OK ≤ SK := by
    have h1 : OK ≤ OI := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp d.comp)
    exact le_inf (h1.trans hOIS) (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hOKY : OK ≤ Y := by
    intro x hx
    refine ⟨Subgroup.mem_sup_left (hSKB (hOKS hx)), Subgroup.le_normalizer hx, fun k hk => ?_⟩
    have hk' : k ∈ Subgroup.normalizer (OK : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact OK.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hk' _).mp (OK.inv_mem hx))
  have hidx : ∃ a : ℕ, (Y ⊓ K).relIndex Y = 2 ^ a := by
    have hYNK : Y ≤ Subgroup.normalizer (K : Set G) := hYX₀.trans hX₀NK
    have e1 : (Y ⊓ K).relIndex Y = K.relIndex (Y ⊔ K) := by
      rw [Subgroup.inf_relIndex_left, A4.relIndex_sup_eq_of_le_normalizer' hYNK]
    have e2 : K.relIndex (W ⊔ K) = K.relIndex W := A4.relIndex_sup_eq_of_le_normalizer' hWNK
    have hle : Y ⊔ K ≤ W ⊔ K := sup_le (hYX₀.trans (sup_le (fun x hx =>
      Subgroup.mem_sup_right hx.1) le_sup_left)) le_sup_right
    have hd1 : K.relIndex (Y ⊔ K) ∣ K.relIndex (W ⊔ K) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex K (Y ⊔ K) (W ⊔ K) le_sup_right hle)
    have hd2 : K.relIndex W ∣ Nat.card W := Subgroup.relIndex_dvd_card K W
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp (hS2.to_le hWS)
    rw [e1]
    rw [e2] at hd1
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hd1.trans (hb ▸ hd2))
    exact ⟨a, ha⟩
  have hOY2 : IsPGroup 2 (pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hSK2 : IsPGroup 2 SK := hS2.to_le inf_le_left
  have hSKO : SK ≤ Subgroup.normalizer ((pCoreOf 2 Y : Subgroup G) : Set G) :=
    (hSKB.trans (le_sup_left.trans hX₀Y)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hC2 : IsPGroup 2 C := hSK2.to_sup_of_normal_right' hOY2 hSKO
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    refine mem_normalizer_sup_ch6 hx.2 ?_
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y
      (hX₀Y (Subgroup.mem_sup_left hx))
  have hRC : R ≤ C := by
    intro r hr
    obtain ⟨sb, hsb, hsr⟩ := d.exists_phi_R_eq_conj hI kf1 h23 hr
    obtain ⟨⟨s, hsK⟩, hs, rfl⟩ := hsb
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
    have hsN : s ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hsK
    have hyN : s⁻¹ * r ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hsN) (hRNK hr)
    have hy1 : phiK K ⟨s⁻¹ * r, hyN⟩ = 1 := by
      have e : (⟨s⁻¹ * r, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨s, hsN⟩)⁻¹ * ⟨r, hRNK hr⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hsr, phiK_of_mem K ⟨s, hsK⟩, inv_mul_cancel]
    have hyY : s⁻¹ * r ∈ Y := by
      refine ⟨X₀.mul_mem (X₀.inv_mem (Subgroup.mem_sup_left (hSKB hs)))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left hr)),
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hyN, fun k hk => ?_⟩
      exact (phiK_eq_one_iff d.quasi _).mp hy1 k hk
    have hy2 : ∃ m : ℕ, (s⁻¹ * r) ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := hS2 ⟨s⁻¹ * r, S.mul_mem (S.inv_mem hs.1) (hRS hr)⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hyO := mem_pCoreOf_of_relIndex_two_pow inf_le_left
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hOKY (hYX₀.trans hX₀OK) hidx
      (fun z hz y hy => hy.2.2 z hz.2) hyY hy2
    have e : r = s * (s⁻¹ * r) := by group
    rw [e]
    exact C.mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hyO)
  have hOIY : OI ≤ Y := by
    intro x hx
    refine ⟨Subgroup.mem_sup_right (Subgroup.mem_sup_right hx),
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hOINK hx), fun k hk => ?_⟩
    exact (phiK_eq_one_iff d.quasi _).mp (d.phi_eq_one_of_mem_pCoreOf hx) k hk
  have hOIC : OI ≤ C := by
    refine le_trans ?_ le_sup_right
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOIY ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)
    exact (hYX₀.trans hX₀I).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
  have hUC : ch6U T L V ≤ C := ((d.hyp.lemma_6_1_20_one hI.h432).1).trans hOIC
  have hS1 := d.isSylowTwoOf_S1 hI
  have hS1X₀ : ch6S T L V ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (X₀ : Set G) := by
    intro x hx
    have hxI : x ∈ I := hx.1.2
    have hxNK : x ∈ Subgroup.normalizer (K : Set G) := hx.2
    have hxSK : x ∈ Subgroup.normalizer (SK : Set G) := hSKN x hx.1 hxNK
    refine mem_normalizer_sup_ch6 ?_ (mem_normalizer_sup_ch6 ?_ ?_)
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hxNK, F1.mem_normalizer_normalizer hxSK⟩
    · exact (d.hyp.MV_le_normalizer_R hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).1
        ⟨d.hyp.T_le hx.1.1, d.hyp.toHyp611.T_le_normalizer hx.1.1⟩
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I hxI
  have hS1Y : ch6S T L V ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (Y : Set G) :=
    le_normalizer_centralizerMod (fun x hx =>
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hx.2) hS1X₀ (fun x hx => hx.2)
  have hCS1 : C ≤ ch6S T L V ⊓ Subgroup.normalizer (K : Set G) := by
    refine sup_le (le_inf inf_le_left fun x hx => Subgroup.le_normalizer hx.2) ?_
    have hOYS1 : ch6S T L V ⊓ Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer ((pCoreOf 2 Y : Subgroup G) : Set G) :=
      hS1Y.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
    have hsup : IsPGroup 2 ↥((ch6S T L V ⊓ Subgroup.normalizer (K : Set G)) ⊔ pCoreOf 2 Y) :=
      hS1.2.1.to_sup_of_normal_right' hOY2 hOYS1
    have hYle : pCoreOf 2 Y ≤ I ⊓ Subgroup.normalizer (K : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans (hYX₀.trans (le_inf hX₀I hX₀NK))
    have hmax := (A4.isSylowTwoOf_iff_maximal.mp hS1).2.2 _
      (sup_le hS1.1 hYle) hsup le_sup_left
    exact le_sup_right.trans hmax
  have hCS : C ≤ ch6S T L V := hCS1.trans inf_le_left
  have h623 := stmt6_1_23 hI.h432 hI.h6111 hI.h6119 G T M L V n d.hyp l d.l_mem d.l_not
  dsimp only at h623
  exact hBC.trans (h623 C hCS (sup_le hRC hUC))

end Dat625

end CFSG.Quasithin.H13
