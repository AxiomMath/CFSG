module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowFacts
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313He
public import Certificates.Certificate7136

public section

namespace CFSG.Quasithin.H13.KGHe

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms




section Generic

variable {X : Type*} [Group X] [Finite X]

theorem mem_of_mem_normalizer_of_pow {A S : Subgroup X} (hS : IsSylowTwoOf S A) {g : X}
    (hgA : g ∈ A) (hgN : g ∈ Subgroup.normalizer (S : Set X)) {k : ℕ} (hg : g ^ 2 ^ k = 1) :
    g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (Subgroup.zpowers g) := by
    have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (S : Set X) := Subgroup.zpowers_le.mpr hgN
  have hP : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers g) := hS.2.1.to_sup_of_normal_left' hgp hle
  have hSA : S ⊔ Subgroup.zpowers g ≤ A := sup_le hS.1 (Subgroup.zpowers_le.mpr hgA)
  have hidx : S.relIndex (S ⊔ Subgroup.zpowers g) = 1 := by
    have h1 := Subgroup.relIndex_mul_relIndex S (S ⊔ Subgroup.zpowers g) A le_sup_left hSA
    have h2 : ¬ 2 ∣ S.relIndex A := hS.2.2
    have h3 : ¬ 2 ∣ S.relIndex (S ⊔ Subgroup.zpowers g) := fun h =>
      h2 (h1 ▸ Dvd.dvd.mul_right h _)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have h4 : S.relIndex (S ⊔ Subgroup.zpowers g) ∣ 2 ^ n :=
      hn ▸ Subgroup.relIndex_dvd_card S (S ⊔ Subgroup.zpowers g)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    rw [hj] at h3 ⊢
    rcases j with _ | j
    · rfl
    · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero j)) h3
  have := Subgroup.relIndex_eq_one.mp hidx
  exact this (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

theorem mem_inner_of_pow_eq_one {G : Type*} [Group G] [Finite G] (hout : Nat.card (Outer G) ≤ 2)
    {α : MulAut G} {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) : α ∈ inner G := by
  have : Finite (MulAut G) :=
    Finite.of_injective (fun e : MulAut G => (e : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)
  have h1 : (QuotientGroup.mk' (inner G) α) ^ m = 1 := by rw [← map_pow, hα, map_one]
  have h2 : orderOf (QuotientGroup.mk' (inner G) α) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' (inner G) α) ∣ m := orderOf_dvd_of_pow_eq_one h1
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  have h4 : orderOf (QuotientGroup.mk' (inner G) α) = 1 := by
    have h5 : orderOf (QuotientGroup.mk' (inner G) α) ∣ 2 := by
      rcases Nat.lt_or_ge (Nat.card (Outer G)) 2 with h | h
      · have : Nat.card (Outer G) = 1 := by omega
        rw [this] at h2
        exact h2.trans (one_dvd 2)
      · have : Nat.card (Outer G) = 2 := by omega
        rwa [this] at h2
    rcases (Nat.dvd_prime Nat.prime_two).1 h5 with h6 | h6
    · exact h6
    · rw [h6] at h3
      exact absurd (even_iff_two_dvd.mpr h3) (Nat.not_even_iff_odd.mpr hm)
  have h7 := orderOf_eq_one_iff.mp h4
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h7
  exact h7

theorem mem_of_mem_normalizer_inner {G : Type*} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hsn : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → Subgroup.normalizer (P : Set G) ≤ P)
    {P : Subgroup (MulAut G)} (hP : IsSylowTwoOf P (inner G)) {y : MulAut G} (hy : y ∈ inner G)
    (hyN : y ∈ Subgroup.normalizer (P : Set (MulAut G))) : y ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, rfl⟩ := hy
  let φ : G →* ↥(inner G) :=
    (MulAut.conj : G →* MulAut G).codRestrict (inner G) fun x => ⟨x, rfl⟩
  have hφ : ∀ x, (φ x : MulAut G) = MulAut.conj x := fun x => rfl
  let P' : Subgroup G := (P.subgroupOf (inner G)).comap φ
  have hmem : ∀ x : G, x ∈ P' ↔ MulAut.conj x ∈ P := fun x => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hφ]
  have hφinj : Function.Injective φ := fun a b hab =>
    hinj (by rw [← hφ a, ← hφ b, hab])
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hP'syl : IsSylowTwoOf P' ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hP.2.1.comap_of_injective (inner G).subtype Subtype.val_injective).comap_of_injective
        φ hφinj
    · have h1 : P'.index = (P.subgroupOf (inner G)).index :=
        Subgroup.index_comap_of_surjective (P.subgroupOf (inner G)) hφsurj
      show ¬ 2 ∣ P'.relIndex ⊤
      rw [Subgroup.relIndex_top_right, h1]
      exact hP.2.2
  have hhN : h ∈ Subgroup.normalizer (P' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : MulAut.conj (h * x * h⁻¹) = MulAut.conj h * MulAut.conj x * (MulAut.conj h)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [hmem, hmem, e]
    exact Subgroup.mem_normalizer_iff.mp hyN (MulAut.conj x)
  exact (hmem h).mp (hsn P' hP'syl hhN)

omit [Finite X] in
theorem zpow_pow_comm' (y : X) (v : ℤ) (k : ℕ) : (y ^ v) ^ k = (y ^ k) ^ v := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem normalizer_inf_le_of_selfNormalizing {G : Type*} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hsn : ∀ P : Subgroup G, IsSylowTwoOf P ⊤ → Subgroup.normalizer (P : Set G) ≤ P)
    (hout : Nat.card (Outer G) ≤ 2) {A S : Subgroup (MulAut G)}
    (hA : (MulAut.conj : G →* MulAut G).range ≤ A) (hS : IsSylowTwoOf S A) :
    Subgroup.normalizer (S : Set (MulAut G)) ⊓ A ≤ S := by
  have : Finite (MulAut G) :=
    Finite.of_injective (fun e : MulAut G => (e : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)
  intro x hx
  obtain ⟨hxN, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hb : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
    have := Nat.gcd_eq_gcd_ab (2 ^ a) m
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hxn : x ^ (2 ^ a * m) = 1 := hn ▸ pow_orderOf_eq_one x
  set y := (x ^ (2 ^ a)) ^ Nat.gcdA (2 ^ a) m with hy
  set z := (x ^ m) ^ Nat.gcdB (2 ^ a) m with hz
  have hxyz : x = y * z := by
    rw [hy, hz, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hb, zpow_one]
  have hz2 : z ^ 2 ^ a = 1 := by
    rw [hz, zpow_pow_comm', ← pow_mul, mul_comm, hxn, one_zpow]
  have hym : y ^ m = 1 := by
    rw [hy, zpow_pow_comm', ← pow_mul, hxn, one_zpow]
  have hzS : z ∈ S := mem_of_mem_normalizer_of_pow hS (A.zpow_mem (A.pow_mem hxA _) _)
    (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxN _) _) hz2
  have hyN : y ∈ Subgroup.normalizer (S : Set (MulAut G)) :=
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxN _) _
  have hyI : y ∈ inner G := mem_inner_of_pow_eq_one hout hm hym
  have hSI : IsSylowTwoOf (S ⊓ inner G) (inner G) :=
    A4.isSylowTwoOf_inf_normal hS hA (fun g _ => Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => (inner_normal G).conj_mem h hh g, fun hh => by
        have := (inner_normal G).conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this⟩)
  have hyNI : y ∈ Subgroup.normalizer ((S ⊓ inner G : Subgroup (MulAut G)) : Set (MulAut G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hyN h]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (inner_normal G).conj_mem h h2 y⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := (inner_normal G).conj_mem _ h2 y⁻¹
      simpa [mul_assoc] using this
  have hyS : y ∈ S := (Subgroup.mem_inf.mp (mem_of_mem_normalizer_inner hinj hsn hSI hyI hyNI)).1
  rw [hxyz]
  exact S.mul_mem hyS hzS


omit [Finite X] in
theorem getD_mem_or' {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (List.mem_of_getElem? h)

end Generic

section Model

open CFSG.Sporadic.HeldB CFSG.ComponentClassification.GrSLit.HeldFix CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)

@[expose] noncomputable def wordElt (w : List ℕ) : Equiv.Perm (Fin 8330) := (w.map heInnerCP1).prod

theorem wordTabS_nil (m : ℕ) (gs : Array Tab) : wordTabS m gs [] = idTab m := rfl

theorem wordTabS_cons (m : ℕ) (gs : Array Tab) (j : ℕ) (w : List ℕ) :
    wordTabS m gs (j :: w) = comp m gs[j]! (wordTabS m gs w) := rfl

theorem wordElt_cons (j : ℕ) (w : List ℕ) : wordElt (j :: w) = heInnerCP1 j * wordElt w := by
  simp [wordElt]

theorem hfC1Tabs_size : hfC1Tabs.size = 9 := by
  rw [hfC1Tabs, Array.size_ofFn]

theorem tabRep_wordTabS
    {w : List ℕ} (hw : ∀ j ∈ w, j < 9) :
    TabRep (wordTabS 8330 hfC1Tabs w) (wordElt w) := by
  induction w with
  | nil =>
    rw [wordTabS_nil, show wordElt [] = 1 from rfl]
    exact TabRep.idTab
  | cons j w ih =>
    have hj : j < hfC1Tabs.size := by rw [hfC1Tabs_size]; exact hw j List.mem_cons_self
    rw [wordTabS_cons, wordElt_cons]
    exact (tabRep_hfC1Tabs j hj).comp (ih fun k hk => hw k (List.mem_cons_of_mem _ hk))

theorem wordElt_mem {w : List ℕ}
    (hw : ∀ j ∈ w, j < 9) : wordElt w ∈ centralizerIn heP heT1P :=
  heInnerGrp1_le (heInnerGrp1.list_prod_mem fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨j, hw j hj, rfl⟩)

theorem not_mem_hfT_of
    {x : Equiv.Perm (Fin 8330)} {X : Tab} (hX : TabRep X x)
    (h : notInOK hfTEnum32.tabs (hfRes X) = true) : x ∉ hfT := by
  intro hx
  have h1 : TabRep (hfRes X) (hfPhiT ⟨x, hx⟩) :=
    hfDelta32_points.tabRep_restrHom hfT hfT_preserves ⟨x, hx⟩ hX.2
  exact not_mem_of_notInOK enumerates_hfPhiT h h1 ⟨_, rfl⟩

@[expose] noncomputable def gW (i : ℕ) : Equiv.Perm (Fin 8330) :=
  wordElt (Certificates.HeNorm.words.getD i [])

theorem words_lt (i : ℕ) :
    ∀ j ∈ Certificates.HeNorm.words.getD i [], j < 9 := by
  intro j hj
  rcases getD_mem_or' Certificates.HeNorm.words i [] with h | h
  · exact Certificates.certificate7136.1 _ h j hj
  · rw [h] at hj
    simp at hj

theorem exists_conj_not_mem
    {i j : ℕ} (hi : i < 8) (hj : j < 8) (hij : i ≠ j) :
    ∃ t ∈ hfT, (gW j)⁻¹ * gW i * t * ((gW j)⁻¹ * gW i)⁻¹ ∉ hfT := by
  obtain ⟨-, hwi, hhi, hc⟩ := Certificates.certificate7136
  obtain ⟨k, hk, hkc⟩ := hc i hi j hj hij
  have hk' : k < hfTTabs.size := by rw [hfTTabs_size]; exact hk
  have ri : TabRep (Certificates.HeNorm.wt i) (gW i) := tabRep_wordTabS (words_lt i)
  have rj : TabRep (Certificates.HeNorm.wt j) (gW j) := tabRep_wordTabS (words_lt j)
  have rji : TabRep (Certificates.HeNorm.wti j) (gW j)⁻¹ :=
    rj.inv (hwi j hj).1 (hwi j hj).2
  have rh : TabRep (Certificates.HeNorm.hT i j) ((gW j)⁻¹ * gW i) := rji.comp ri
  have rhi : TabRep (Certificates.HeNorm.hTi i j) ((gW j)⁻¹ * gW i)⁻¹ :=
    rh.inv (hhi i hi j hj).1 (hhi i hi j hj).2
  have rc : TabRep (Certificates.HeNorm.cj i j k)
      ((gW j)⁻¹ * gW i * hfTL k * ((gW j)⁻¹ * gW i)⁻¹) :=
    (rh.comp (tabRep_hfTTabs k hk')).comp rhi
  exact ⟨hfTL k, hfTL_mem_hfT hk, not_mem_hfT_of rc hkc⟩

theorem factorization_21504 : (21504 : ℕ).factorization 2 = 10 := by
  rw [show (21504 : ℕ) = 2 ^ 10 * 21 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21)]
  simp

theorem mem_hfT_of_mem_normalizer_C
    {x : Equiv.Perm (Fin 8330)} (hxC : x ∈ centralizerIn heP heT1P)
    (hxN : x ∈ Subgroup.normalizer (hfT : Set (Equiv.Perm (Fin 8330)))) : x ∈ hfT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : hfT ≤ centralizerIn heP heT1P := hfT_le_grp1.trans heInnerGrp1_le
  have hcardC : Nat.card (centralizerIn heP heT1P) = 21504 := card_heP_cent1
  have hcardT : Nat.card (hfT.subgroupOf (centralizerIn heP heT1P)) = 1024 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv, card_hfT]
  let P : Sylow 2 ↥(centralizerIn heP heT1P) :=
    Sylow.ofCard (hfT.subgroupOf (centralizerIn heP heT1P))
      (by rw [hcardT, hcardC, factorization_21504]; norm_num)
  have hP : (P : Subgroup ↥(centralizerIn heP heT1P)) = hfT.subgroupOf (centralizerIn heP heT1P) :=
    Sylow.coe_ofCard _ _
  let g : Fin 8 → ↥(centralizerIn heP heT1P) := fun i => ⟨gW i, wordElt_mem (words_lt i)⟩
  have hinj : Function.Injective (fun i : Fin 8 => g i • P) := by
    intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    obtain ⟨t, ht, hnot⟩ := exists_conj_not_mem i.2 j.2 hne'
    apply hnot
    have htP : (⟨t, hTC ht⟩ : ↥(centralizerIn heP heT1P)) ∈ (P : Subgroup _) := by
      rw [hP, Subgroup.mem_subgroupOf]
      exact ht
    have h1 : MulAut.conj (g i) • (⟨t, hTC ht⟩ : ↥(centralizerIn heP heT1P)) ∈
        ((g j • P : Sylow 2 _) : Subgroup _) := by
      have := hij
      simp only at this
      rw [← this, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj (g i)) _ htP
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : ((g j)⁻¹ * (g i * ⟨t, hTC ht⟩ * (g i)⁻¹) * g j : ↥(centralizerIn heP heT1P)) ∈
        (P : Subgroup _) := by
      have e : (MulAut.conj (g j))⁻¹ • MulAut.conj (g i) •
          (⟨t, hTC ht⟩ : ↥(centralizerIn heP heT1P)) =
          (g j)⁻¹ * (g i * ⟨t, hTC ht⟩ * (g i)⁻¹) * g j := by
        rw [← map_inv, MulAut.smul_def, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply,
          inv_inv]
      rw [← e]
      exact h1
    rw [hP, Subgroup.mem_subgroupOf] at h2
    have e2 : (((g j)⁻¹ * (g i * ⟨t, hTC ht⟩ * (g i)⁻¹) * g j : ↥(centralizerIn heP heT1P)) :
        Equiv.Perm (Fin 8330)) = (gW j)⁻¹ * gW i * t * ((gW j)⁻¹ * gW i)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, g]
      group
    rw [e2] at h2
    exact h2
  have h8 : 8 ≤ Nat.card (Sylow 2 ↥(centralizerIn heP heT1P)) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  rw [Sylow.card_eq_index_normalizer P] at h8
  set N : Subgroup ↥(centralizerIn heP heT1P) :=
    Subgroup.normalizer ((P : Subgroup ↥(centralizerIn heP heT1P)) : Set ↥(centralizerIn heP heT1P))
    with hN
  have hmul := Subgroup.card_mul_index N
  rw [hcardC] at hmul
  have hPN : (P : Subgroup ↥(centralizerIn heP heT1P)) ≤ N := Subgroup.le_normalizer
  have hdvd : 1024 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hPN
    rwa [hP, hcardT] at this
  obtain ⟨d, hd⟩ := hdvd
  rw [hd] at hmul
  have hdI : d * N.index = 21 := by
    have : 1024 * (d * N.index) = 1024 * 21 := by
      rw [← mul_assoc, hmul]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hd1 : d = 1 := by
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdI
    have hle : d * 8 ≤ 21 := hdI ▸ Nat.mul_le_mul_left d h8
    have hd2 : d ≤ 2 := by omega
    interval_cases d <;> omega
  have hNP : (P : Subgroup ↥(centralizerIn heP heT1P)) = N :=
    Subgroup.eq_of_le_of_card_ge hPN (by rw [hd, hd1, hP, hcardT])
  have hxP : (⟨x, hxC⟩ : ↥(centralizerIn heP heT1P)) ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff]
    intro y
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hxN y
  rw [← hNP, hP, Subgroup.mem_subgroupOf] at hxP
  exact hxP

theorem commute_of_mem_normalizer
    {x : Equiv.Perm (Fin 8330)}
    (hxN : x ∈ Subgroup.normalizer (hfT : Set (Equiv.Perm (Fin 8330)))) :
    x * heT1P = heT1P * x := by
  have ht1 : heT1P ∈ hfT := by simpa [hfTL] using hfTL_mem_hfT (j := 0) (by norm_num)
  have hcomm : ∀ t ∈ hfT, t * heT1P = heT1P * t := fun t ht =>
    (mem_centralizerIn.1 (heInnerGrp1_le (hfT_le_grp1 ht))).2
  have hyT : x * heT1P * x⁻¹ ∈ hfT := (Subgroup.mem_normalizer_iff.mp hxN heT1P).mp ht1
  have hxiN : x⁻¹ ∈ Subgroup.normalizer (hfT : Set (Equiv.Perm (Fin 8330))) := inv_mem hxN
  have hyZ : (⟨x * heT1P * x⁻¹, hyT⟩ : ↥hfT) ∈ Subgroup.center ↥hfT := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hs' : x⁻¹ * s * x⁻¹⁻¹ ∈ hfT :=
      (Subgroup.mem_normalizer_iff.mp hxiN s).mp s.2
    rw [inv_inv] at hs'
    have hc := hcomm _ hs'
    simp only [Subgroup.coe_mul]
    calc (s : Equiv.Perm (Fin 8330)) * (x * heT1P * x⁻¹)
        = x * ((x⁻¹ * s * x) * heT1P) * x⁻¹ := by group
      _ = x * (heT1P * (x⁻¹ * s * x)) * x⁻¹ := by rw [hc]
      _ = x * heT1P * x⁻¹ * s := by group
  have ht1Z : (⟨heT1P, ht1⟩ : ↥hfT) ∈ Subgroup.center ↥hfT := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hcomm s s.2)
  have hne1 : (⟨⟨heT1P, ht1⟩, ht1Z⟩ : Subgroup.center ↥hfT) ≠ 1 := fun h =>
    heT1P_ne_one (congrArg (fun z : Subgroup.center ↥hfT => ((z : ↥hfT) : Equiv.Perm (Fin 8330))) h)
  have hne2 : (⟨⟨x * heT1P * x⁻¹, hyT⟩, hyZ⟩ : Subgroup.center ↥hfT) ≠ 1 := fun h => by
    have h1 := congrArg (fun z : Subgroup.center ↥hfT => ((z : ↥hfT) : Equiv.Perm (Fin 8330))) h
    simp only [OneMemClass.coe_one] at h1
    apply heT1P_ne_one
    calc heT1P = x⁻¹ * (x * heT1P * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥hfT)).mp card_center_hfT
  have e := (hz _ hne2).trans (hz _ hne1).symm
  have e' := congrArg (fun z : Subgroup.center ↥hfT => ((z : ↥hfT) : Equiv.Perm (Fin 8330))) e
  simp only at e'
  calc x * heT1P = (x * heT1P * x⁻¹) * x := by group
    _ = heT1P * x := by rw [e']

theorem mem_hfT_of_mem_normalizer
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heP)
    (hxN : x ∈ Subgroup.normalizer (hfT : Set (Equiv.Perm (Fin 8330)))) : x ∈ hfT :=
  mem_hfT_of_mem_normalizer_C (mem_centralizerIn.2 ⟨hx, commute_of_mem_normalizer hxN⟩) hxN

end Model

section Transport

open CFSG.Sporadic.HeldB CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)

variable {Q : Type*} [Group Q] [Finite Q]

theorem selfNormalizing_of_mulEquiv
    (e : Q ≃* ↥heP) (P : Subgroup Q) (hP : IsSylowTwoOf P ⊤) :
    Subgroup.normalizer (P : Set Q) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTP : hfT ≤ heP := hfT_le_heP
  let P₀ : Subgroup Q := (hfT.subgroupOf heP).comap e.toMonoidHom
  have hmem : ∀ x : Q, x ∈ P₀ ↔ ((e x : ↥heP) : Equiv.Perm (Fin 8330)) ∈ hfT := fun x => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  have hP₀card : Nat.card P₀ = 1024 := by
    have h1 : Nat.card P₀ = Nat.card (hfT.subgroupOf heP) := by
      rw [Nat.card_congr (P₀.equivMapOfInjective e.toMonoidHom e.injective).toEquiv,
        show P₀.map e.toMonoidHom = hfT.subgroupOf heP from
          Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective _]
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv, card_hfT]
  have hQcard : Nat.card Q = 4030387200 := (Nat.card_congr e.toEquiv).trans card_heP
  have hP₀syl : IsSylowTwoOf P₀ ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 10) (by rw [hP₀card]; norm_num), ?_⟩
    have hmul := Subgroup.card_mul_index P₀
    rw [hP₀card, hQcard] at hmul
    show ¬ 2 ∣ P₀.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    omega
  have hsn₀ : Subgroup.normalizer (P₀ : Set Q) ≤ P₀ := by
    intro x hx
    rw [hmem]
    refine mem_hfT_of_mem_normalizer (e x).2 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ heP
    · have h1 := Subgroup.mem_normalizer_iff.mp hx (e.symm ⟨y, hy⟩)
      rw [hmem, hmem] at h1
      simpa using h1
    · constructor
      · intro h
        exact absurd (hTP h) hy
      · intro h
        exfalso
        apply hy
        have h2 := hTP h
        set ex : Equiv.Perm (Fin 8330) := ((e x : ↥heP) : Equiv.Perm (Fin 8330)) with hex
        have h3 : ex⁻¹ * (ex * y * ex⁻¹) * ex ∈ heP :=
          heP.mul_mem (heP.mul_mem (heP.inv_mem (e x).2) h2) (e x).2
        simpa [mul_assoc] using h3
  obtain ⟨h, -, rfl⟩ := hP₀syl.exists_conj hP
  intro x hx
  have hx' : h⁻¹ * x * h ∈ Subgroup.normalizer (P₀ : Set Q) := by
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    have h1 := hx (h * y * h⁻¹)
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    constructor
    · intro hy
      obtain ⟨z, hz, hzz⟩ := h1.mp ⟨y, hy, rfl⟩
      have : h⁻¹ * x * h * y * (h⁻¹ * x * h)⁻¹ = z := by
        calc h⁻¹ * x * h * y * (h⁻¹ * x * h)⁻¹ = h⁻¹ * (x * (h * y * h⁻¹) * x⁻¹) * h := by group
          _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hzz]
          _ = z := by group
      rw [this]
      exact hz
    · intro hy
      obtain ⟨z, hz, hzz⟩ := h1.mpr ⟨_, hy, by group⟩
      have : y = z := by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hzz]
          _ = z := by group
      rw [this]
      exact hz
  refine ⟨h⁻¹ * x * h, hsn₀ hx', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

omit [Finite Q] in
theorem conj_injective_of_mulEquiv
    (e : Q ≃* ↥heP) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  have hsimple : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ heP_simple e
  have ht1P : heT1P ∈ heP := (mem_centralizerIn.1 (heInnerGrp1_le heT1P_mem_grp1)).1
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      have hall : ∀ y ∈ heP, y * heT1P = heT1P * y := by
        intro y hy
        have hc : e.symm ⟨heT1P, ht1P⟩ ∈ Subgroup.center Q := h ▸ Subgroup.mem_top _
        have h1 := Subgroup.mem_center_iff.mp hc (e.symm ⟨y, hy⟩)
        have h2 := congrArg (fun w => ((e w : ↥heP) : Equiv.Perm (Fin 8330))) h1
        simpa using h2
      have hC : centralizerIn heP heT1P = heP :=
        le_antisymm inf_le_left fun y hy => mem_centralizerIn.2 ⟨hy, hall y hy⟩
      have h1 := card_heP_cent1
      rw [hC, card_heP] at h1
      norm_num at h1
  intro a b hab
  have hc : a⁻¹ * b ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut Q => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.mp hc

omit [Finite Q] in
theorem card_outer_le_of_mulEquiv
    (e : Q ≃* ↥heP) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) ≤ 2 :=
  CFSG.Sporadic.Schreier.outer_card_le_of_equiv
    (heConjR_facts CFSG.Sporadic.Schreier.AT_He_Schreier.1).2.2.2.le e

end Transport

theorem factAutHeSylow_holds :
    CFSG.Quasithin.H13.FactAutHeSylow := by
  intro Q _ _ he A S hA hS
  obtain ⟨e₀⟩ := he
  let e : Q ≃* ↥CFSG.Sporadic.HeldB.heP := e₀.trans CFSG.Sporadic.HeldB.heEquivP
  exact normalizer_inf_le_of_selfNormalizing (conj_injective_of_mulEquiv e)
    (selfNormalizing_of_mulEquiv e) (card_outer_le_of_mulEquiv e) hA hS

end CFSG.Quasithin.H13.KGHe
