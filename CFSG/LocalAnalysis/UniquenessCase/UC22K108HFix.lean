module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rS207
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108HLe
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22r

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

theorem F10.k108X_of_k108H207 (hK : F10.K108H207) {Gh : Type} [Group Gh] [Finite Gh] {S T X M : Subgroup Gh}
    [hSn : S.Normal] (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hC : centralizer (S : Set Gh) = ⊥) (hshape : F10.IsList207 ↥S)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hX : (Nat.card X).Prime) (hXodd : Odd (Nat.card X))
    (hXT : Permutes X T) (hSX : S ⊔ X = ⊤) (hTM : T ≤ M) (hXM : X ≤ M)
    (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) : S ≤ M := by
  haveI : Fact (Nat.card X).Prime := ⟨hX⟩
  haveI hcyc : IsCyclic ↥X := isCyclic_of_prime_card (p := Nat.card X) rfl
  exact hK Gh S hSn hS hnab hC hshape T X ⟨hT, inferInstance, hXodd, hXT, fun p hp _ =>
    (CFSG.SectionRank.pRank_le_one_of_isCyclic hp hcyc).trans (by norm_num)⟩ hSX X M le_rfl hX hXodd
    hTM hXM hstar

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_le_of_k108H207 (hK : F10.K108H207) {K X T' M : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hX : X = Subgroup.zpowers x) (hxo : orderOf x = q)
    (hXK : X ≤ normalizer (K : Set G)) (hKq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hshape : F10.IsList207 (uc22p22rKt K))
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' K) (hperm : Permutes X T')
    (hT'M : T' ≤ M) (hXM : X ≤ M) (hO2 : pCoreOf 2 K ≤ M)
    (hZ : ∀ k : ↥K, uc22p22rPsi K k = 1 → (k : G) ∈ M)
    (h0 : ∀ Y : Subgroup G, X ≤ Y → Y ≤ M → ∀ n ∈ K ⊔ X, n ∈ normalizer (Y : Set G) → n ∈ M)
    (hstar : ∀ g ∈ K ⊔ X, (∀ y ∈ X, g⁻¹ * y * g ∈ M) → g ∈ M) : K ≤ M := by
  by_contra hKM
  have hxq : x ^ q = 1 := hxo ▸ pow_orderOf_eq_one x
  have hXq : Nat.card X = q := by rw [hX, Nat.card_zpowers, hxo]
  have hXc := uc22p22r_zpowers_comm (x := x)
  rw [← hX] at hXc
  haveI hSn : (uc22p22rS K X hXK).Normal := uc22p22rS_normal hXK
  have hker : ∀ n : ↥(K ⊔ X), uc22p22rPi K X hXK n = 1 → (n : G) ∈ M := fun n hn =>
    uc22p22r_ker_le hXK hXc hKq hXM hZ h0 n ((uc22p22rPi_eq_one_iff hXK n).1 hn)
  have hxX : x ∈ X := hX ▸ Subgroup.mem_zpowers x
  have hxN : x ∈ K ⊔ X := Subgroup.mem_sup_right hxX
  have hρ1 := uc22p22r_rho_ne_one hXK hq hq2 hX hxq hKq hO2 h0 hXM hKM
  have hXcard : Nat.card (uc22p22rImg hXK X) = q := by
    have hdvd : Nat.card (uc22p22rImg hXK X) ∣ q := by
      have h1 : Nat.card (uc22p22rImg hXK X) ∣ Nat.card (X.subgroupOf (K ⊔ X)) := by
        rw [uc22p22rImg_eq_map]
        exact Subgroup.card_map_dvd _ _
      have h2 : Nat.card (X.subgroupOf (K ⊔ X)) = q := by
        rw [← hXq]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      rwa [h2] at h1
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exfalso
      have hone : uc22p22rPi K X hXK ⟨x, hxN⟩ ∈ uc22p22rImg hXK X :=
        (uc22p22r_mem_img hXK).2 ⟨⟨x, hxN⟩, hxX, rfl⟩
      have hsub : Subsingleton (uc22p22rImg hXK X) := Nat.card_eq_one_iff_unique.1 h |>.1
      have h2 : uc22p22rPi K X hXK ⟨x, hxN⟩ = 1 := by
        have := Subsingleton.elim (⟨_, hone⟩ : uc22p22rImg hXK X) 1
        exact congrArg Subtype.val this
      exact hρ1 ((uc22p22rPi_eq_one_iff hXK _).1 h2)
    · exact h
  have hshape' : F10.IsList207 ↥(uc22p22rS K X hXK) := hshape.of_mulEquiv (uc22p22rSEquiv hXK hKq)
  have hM : uc22p22rS K X hXK ≤ uc22p22rImg hXK M :=
    F10.k108X_of_k108H207 hK (uc22p22rS_simple hXK hKq) (uc22p22rS_nonab hXK hKq)
      (uc22p22rS_centralizer hXK hKq) hshape' (uc22p22r_sylow_img hXK hq hq2 hXq hT')
      (hXcard ▸ hq) (hXcard ▸ hq.odd_of_ne_two hq2)
      (uc22p22r_permutes_img hXK hT'.le hperm) (uc22p22rS_sup_img_eq_top hXK)
      (uc22p22r_img_mono hXK hT'M) (uc22p22r_img_mono hXK hXM) (by
        intro ĝ hĝ
        obtain ⟨γ, rfl⟩ := uc22p22rPi_surjective hXK ĝ
        have hγM : (γ : G) ∈ M := by
          apply hstar (γ : G) γ.2
          intro y hy
          have hyN : y ∈ K ⊔ X := Subgroup.mem_sup_right hy
          have h1 := hĝ (uc22p22rPi K X hXK ⟨y, hyN⟩)
            ((uc22p22r_mem_img hXK).2 ⟨⟨y, hyN⟩, hy, rfl⟩)
          obtain ⟨m, hmM, hmπ⟩ := (uc22p22r_mem_img hXK).1 h1
          have h2 : uc22p22rPi K X hXK (m⁻¹ * (γ⁻¹ * ⟨y, hyN⟩ * γ)) = 1 := by
            simp only [map_mul, map_inv, hmπ]
            group
          have h3 := hker _ h2
          have h4 : (γ : G)⁻¹ * y * γ = (m : G) * ((m : G)⁻¹ * ((γ : G)⁻¹ * y * γ)) := by group
          rw [h4]
          exact M.mul_mem hmM (by simpa using h3)
        exact (uc22p22r_mem_img hXK).2 ⟨γ, hγM, rfl⟩)
  apply hKM
  intro k hk
  have hkN : k ∈ K ⊔ X := Subgroup.mem_sup_left hk
  have hmem : uc22p22rPi K X hXK ⟨k, hkN⟩ ∈ uc22p22rImg hXK M :=
    hM (uc22p22rPi_mem_S hXK ⟨k, hkN⟩ hk)
  obtain ⟨m, hmM, hmπ⟩ := (uc22p22r_mem_img hXK).1 hmem
  have h1 : uc22p22rPi K X hXK (m⁻¹ * ⟨k, hkN⟩) = 1 := by
    rw [map_mul, map_inv, hmπ, inv_mul_cancel]
  have h2 := hker _ h1
  have h3 : k = (m : G) * ((m : G)⁻¹ * k) := by group
  rw [h3]
  exact M.mul_mem hmM (by simpa using h2)

section Main


theorem uc22p22r_fix108h_of_k108H207 (D : Data G) (hK : F10.K108H207) (h201 : S20_1_124 D)
    (h204 : S20_4 D) (h207 : S20_7 D) : Fix108H D := by
  intro h1930 H hH q hq hq2 X hXHM hXq hXperm
  by_contra hcon
  have hXH : X ≤ H := hXHM.trans inf_le_left
  have hXM : X ≤ D.M := hXHM.trans inf_le_right
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic ↥X := isCyclic_of_prime_card hXq
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  set x : G := (g : G) with hxdef
  have hX : X = Subgroup.zpowers x := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩
    · intro hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact X.zpow_mem g.2 i
  have hxo : orderOf x = q := by
    rw [← Nat.card_zpowers, ← hX]
    exact hXq
  have hxX : x ∈ X := g.2
  have hxH : x ∈ H := hXH hxX
  have hXexp : ∀ u ∈ X, u ^ q = 1 := by
    intro u hu
    have h1 : (⟨u, hu⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    rw [hXq] at h1
    simpa using congrArg Subtype.val h1
  have hU : ∀ h ∈ H, (∀ y ∈ X, h⁻¹ * y * h ∈ D.M) → h ∈ D.M := by
    intro h hh hy
    by_contra hhM
    apply hcon
    refine ⟨h, hh, hhM, fun z hz => ?_⟩
    have h1 := hy _ ((uc22p22f_mem_conj X h z).1 hz)
    have e : h⁻¹ * (h * z * h⁻¹) * h = z := by group
    rwa [e] at h1
  obtain ⟨L, K, hL, hKc, -, hKM⟩ := uc22p22r_exists_K D h204 h1930 hH
  obtain ⟨hKsub, hKperf⟩ := uc22p22r_K_subnormal hL hKc
  have hKH : K ≤ H := hKsub.le
  have hOinf : OInf H ≤ D.M := (h201 h1930 H hH).2.2
  have hTH : D.T ≤ H := hH.1
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf H) ⊤ := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hTH le_top
    have h2 : CFSG.ABGLocalTools.IsSylowOf 2 ((D.T.subgroupOf H).map H.subtype)
        ((⊤ : Subgroup ↥H).map H.subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_top, Subgroup.range_subtype]
      exact h1
    exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).1 h2
  have hR : CFSG.solvableRadical ↥H ≤ D.M.subgroupOf H := fun r hr => hOinf ⟨r, hr, rfl⟩
  have hU' : ∀ h : ↥H, h⁻¹ * (⟨x, hxH⟩ : ↥H) * h ∈ D.M.subgroupOf H → h ∈ D.M.subgroupOf H := by
    intro h hh
    show (h : G) ∈ D.M
    apply hU h h.2
    intro y hy
    rw [hX] at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : (h : G)⁻¹ * x * (h : G) ∈ D.M := hh
    have e : (h : G)⁻¹ * x ^ i * (h : G) = ((h : G)⁻¹ * x * (h : G)) ^ i := by
      simpa using (conj_zpow (a := (h : G)⁻¹) (b := x) (i := i)).symm
    rw [e]
    exact D.M.zpow_mem h1 i
  have hNR : ∀ n ∈ (uc22p22rPhi hKH).ker,
      ((n : ↥(K.subgroupOf H)) : ↥H) ∈ CFSG.solvableRadical ↥H := by
    intro n hn
    obtain ⟨r, hr, hrn⟩ := uc22p22r_pCoreOf_le_oinf hKsub (uc22p22rPhi_ker hKH n hn)
    have : r = ((n : ↥(K.subgroupOf H)) : ↥H) := Subtype.ext hrn
    rw [← this]
    exact hr
  have hKM' : ¬ K.subgroupOf H ≤ D.M.subgroupOf H := by
    intro h
    apply hKM
    intro k hk
    exact h (show (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H from hk)
  have hxN' := uc22p22r_normalizes hq (x := (⟨x, hxH⟩ : ↥H)) (by rw [Subgroup.orderOf_mk]; exact hxo)
    hT' (fun t ht => D.sylowM.le ht) (show x ∈ D.M from hXM hxX) hR hU'
    (uc22p22r_isPerfect_subgroupOf hKH hKperf) hKsub.subgroupOf (N := (uc22p22rPhi hKH).ker) hNR
    (uc22p22r_quasisimple_quot hKH hKc.2.2) hKM'
  have hxK : x ∈ normalizer (K : Set G) := uc22p22r_mem_normalizer_of_subgroupOf hKH hxH hxN'
  have hXK : X ≤ normalizer (K : Set G) := by
    rw [hX]
    exact Subgroup.zpowers_le.2 hxK
  have hshape := uc22p22r_shape207 D h207 h1930 hL.1 hKc
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    uc22p22r_fo_sylow_inf (D.sylowG.of_le hTH le_top) hKsub
  have hperm : Permutes X (D.T ⊓ K) :=
    uc22p22r_permutes_inf hq hq2 hXexp hXK D.sylowM.isPGroup hXperm
  have hO2 : pCoreOf 2 K ≤ D.M := (uc22p22r_pCoreOf_le_oinf hKsub).trans hOinf
  have hZ : ∀ k : ↥K, uc22p22rPsi K k = 1 → (k : G) ∈ D.M := by
    intro k hk
    have hkZ : k ∈ uc22p22rZK K := by
      rw [uc22p22rZK_eq_ker]
      exact MonoidHom.mem_ker.2 hk
    exact hOinf (uc22p22rZK_le_oinf hKsub ⟨k, hkZ, rfl⟩)
  have h0 : ∀ Y : Subgroup G, X ≤ Y → Y ≤ D.M → ∀ n ∈ K ⊔ X, n ∈ normalizer (Y : Set G) →
      n ∈ D.M := by
    intro Y hXY hYM n hn hnY
    apply hU n (sup_le hKH hXH hn)
    intro y hy
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnY) y).1 (hXY hy)
    exact hYM (by simpa using h1)
  have hstar : ∀ g ∈ K ⊔ X, (∀ y ∈ X, g⁻¹ * y * g ∈ D.M) → g ∈ D.M := fun g hg hy =>
    hU g (sup_le hKH hXH hg) hy
  exact hKM (uc22p22r_le_of_k108H207 hK hq hq2 hX hxo hXK hKc.2.2 hshape hSyl hperm
    (inf_le_left.trans D.sylowM.le) hXM hO2 hZ h0 hstar)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
