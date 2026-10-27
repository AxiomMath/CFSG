module

public import CFSG.Milestones.ASVolI.C3
public import CFSG.Milestones.ASVolI.C2ChiBlocks
public import CFSG.Quasithin.Background.C35InspAll
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Background.C31NonLie
public import CFSG.Quasithin.Background.C35Pf

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint in
theorem burnsideC3h_lie2Types_of_evenLieType
    {S : Type} [Group S] [Finite S]
    (hSQT : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2)
    (hE : EvenLieType S) : C31Lie2Types S := by
  obtain ⟨t, n, f, hadm, hm⟩ := hE
  rcases hm with ⟨ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hm⟩
  · rcases CFSG.SectionRank.ClassicalEven.sqt_even_classical_restriction hSQT hm with
        ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, hn, rfl⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inl ⟨hf, hm⟩⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn, hm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))⟩))))
  · rcases CFSG.SectionRank.sqt_exceptional_restriction hSQT (Or.inl ⟨t, 2, f, ht, hm⟩) with
        ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hodd, hf, hm⟩ | hm | ⟨f, hodd, hf, hm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hodd, hf, hm⟩))))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩))))))⟩))))
  · rcases CFSG.SectionRank.sqt_exceptional_restriction hSQT (Or.inr (Or.inl ⟨t, 2, f, ht, hm⟩)) with
        ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hodd, hf, hm⟩ | hm | ⟨f, hodd, hf, hm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hodd, hf, hm⟩))))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩))))))⟩))))
  · rcases CFSG.SectionRank.sqt_exceptional_restriction hSQT (Or.inr (Or.inr ⟨2, f, hm⟩)) with
        ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hodd, hf, hm⟩ | hm | ⟨f, hodd, hf, hm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hm⟩)))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hodd, hf, hm⟩))))))⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩))))))⟩))))

open CFSG.Open hiding StatedSL StatedSp in
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
theorem burnsideC3h_pRank_of_isComponentOf
    {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hH : IsSQTKIn H)
    (hK : CFSG.Open.IsComponentOf K H) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)) ≤ 2 := by
  have hcat : CFSG.SectionRank.IsSQTKCat ↥H := by
    refine ⟨fun p hp hp2 => ?_, hH.2⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact sqt_iff.mp hH.1 p hp hp2
  have hq : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  let e₁ : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
  let N : Subgroup ↥(K.subgroupOf H) := (Subgroup.center ↥K).comap e₁.toMonoidHom
  have : N.Normal := Subgroup.Normal.comap inferInstance _
  let e : ↥(K.subgroupOf H) ⧸ N ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr N (Subgroup.center ↥K) e₁
      (Subgroup.map_comap_eq_self_of_surjective e₁.surjective _)
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  have : IsSimpleGroup (↥(K.subgroupOf H) ⧸ N) := e.isSimpleGroup
  have hnonab : ∃ a b : ↥(K.subgroupOf H) ⧸ N, a * b ≠ b * a :=
    nonab_of_mulEquiv e.symm hq.2.2
  obtain ⟨hSQT, -⟩ :=
    CFSG.SectionRank.sqt_catalog_of_simple_section_of_sqtk hcat (K.subgroupOf H) N hnonab
  exact CFSG.SectionRank.isStronglyQuasithin_iff.1 (CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars in
open CFSG.Quasithin CFSG.Quasithin.C35 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
@[expose] def burnsideC3h_LeviType (Y : Type) [Group Y] : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m Y) ∨ (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m Y) ∨ IsPSL 3 2 1 Y

open CFSG.Quasithin.C35 in
theorem burnsideC3h_psl2_ne_sp4 {m k : ℕ} (hk : 2 ≤ k) :
    2 ^ m * (4 ^ m - 1) ≠ (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
  intro h
  have hq : 4 ≤ 2 ^ k := (Nat.pow_le_pow_right (by norm_num) hk : 2 ^ 2 ≤ 2 ^ k)
  have hev : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq1 : 1 ≤ 2 ^ k := by omega
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, Nat.sub_self, mul_zero] at h
    have : 0 < (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) :=
      Nat.mul_pos (by positivity) (Nat.mul_pos (by
        have : 16 ≤ (2 ^ k) ^ 2 := (Nat.pow_le_pow_left hq 2).trans' (by norm_num)
        omega) (by
        have : 256 ≤ (2 ^ k) ^ 4 := (Nat.pow_le_pow_left hq 4).trans' (by norm_num)
        omega))
    omega
  · have hodd1 : Odd (4 ^ m - 1) := odd_pow_sub_one (by decide) hm (by norm_num)
    have hodd2 : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) :=
      (odd_pow_sub_one hev (by norm_num) hq1).mul (odd_pow_sub_one hev (by norm_num) hq1)
    have h' : 2 ^ m * (4 ^ m - 1) = 2 ^ (4 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
      rw [h, mul_comm 4 k, pow_mul]
    have hm4 := eq_of_two_pow_mul_odd hodd1 hodd2 h'
    subst hm4
    set q := 2 ^ k with hqdef
    have e2 : (4 : ℕ) ^ (4 * k) = q ^ 8 := by
      rw [hqdef, ← pow_mul, mul_comm k 8]
      simp only [pow_mul]
      norm_num
    have e1 : (2 : ℕ) ^ (4 * k) = q ^ 4 := by rw [mul_comm 4 k, pow_mul]
    rw [e1, e2] at h'
    have hpos : 0 < q ^ 4 := by positivity
    have hc : q ^ 8 - 1 = ((q ^ 2 - 1) * (q ^ 4 - 1)) := Nat.eq_of_mul_eq_mul_left hpos (by rw [h'])
    have h8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h8, h2, h4] at hc
    nlinarith [hc, hq, pow_pos (show (0 : ℤ) < q by positivity) 4, pow_pos (show (0 : ℤ) < q by positivity) 6]

open CFSG.Quasithin.C35 in
theorem burnsideC3h_sz_ne_sp4 {m k : ℕ} (hm : Odd m) (hk : 2 ≤ k) :
    ((2 ^ m) ^ 2 + 1) * (2 ^ m) ^ 2 * (2 ^ m - 1) ≠
      (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
  intro h
  have hq : 4 ≤ 2 ^ k := (Nat.pow_le_pow_right (by norm_num) hk : 2 ^ 2 ≤ 2 ^ k)
  have hev : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq1 : 1 ≤ 2 ^ k := by omega
  have hm0 : 0 < m := by obtain ⟨j, rfl⟩ := hm; omega
  have hA : Odd ((2 ^ m) ^ 2 + 1) :=
    (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hm0.ne'⟩, by norm_num⟩ : Even ((2 ^ m) ^ 2)).add_one
  have hB : Odd (2 ^ m - 1) := odd_pow_sub_one (a := 2) (k := m) even_two hm0 (by norm_num)
  have hodd1 : Odd (((2 ^ m) ^ 2 + 1) * (2 ^ m - 1)) := hA.mul hB
  have hodd2 : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) :=
    (odd_pow_sub_one hev (by norm_num) hq1).mul (odd_pow_sub_one hev (by norm_num) hq1)
  have e1 : (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 := by rw [mul_comm, pow_mul]
  have e2 : (2 : ℕ) ^ (4 * k) = (2 ^ k) ^ 4 := by rw [mul_comm, pow_mul]
  have h' : 2 ^ (2 * m) * (((2 ^ m) ^ 2 + 1) * (2 ^ m - 1)) =
      2 ^ (4 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
    rw [e1, e2, ← h]
    ring
  have := eq_of_two_pow_mul_odd hodd1 hodd2 h'
  obtain ⟨j, rfl⟩ := hm
  omega

theorem burnsideC3h_168_ne_sp4 {k : ℕ} (hk : 2 ≤ k) :
    168 ≠ (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
  intro h
  have h8 : 2 ^ 8 ∣ (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
    refine Dvd.dvd.mul_right ?_ _
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  rw [← h] at h8
  omega

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars in
open CFSG.Quasithin CFSG.Quasithin.C35 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
theorem burnsideC3h_noSp4Quot_of_levi {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hS : IsSimpleGroup (ModO2 X)) (ht : burnsideC3h_LeviType (ModO2 X)) :
    CFSG.Quasithin.MS93.MRes.NoSp4Quot X := by
  rintro ⟨k, F, iF, fF, α, hk, hF, hα, hker⟩
  have hcardF : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hF]
  have hsp : Nat.card ↥(StatedSp 2 F) = (2 ^ k) ^ 4 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hcardF]
  let ᾱ : ModO2 X →* ↥(StatedSp 2 F) := QuotientGroup.lift (CFSG.pCore 2 ↥X) α hker
  have hᾱ : Function.Surjective ᾱ := fun y => by
    obtain ⟨x, rfl⟩ := hα y
    exact ⟨(x : ModO2 X), rfl⟩
  have hq : 4 ≤ 2 ^ k := (Nat.pow_le_pow_right (by norm_num) hk : 2 ^ 2 ≤ 2 ^ k)
  have hnt : Nontrivial ↥(StatedSp 2 F) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hsp]
    have h2 : 16 ≤ (2 ^ k) ^ 2 := (Nat.pow_le_pow_left hq 2).trans' (by norm_num)
    have h4 : 256 ≤ (2 ^ k) ^ 4 := (Nat.pow_le_pow_left hq 4).trans' (by norm_num)
    have : 1 ≤ ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 4 - 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  have hinj : Function.Injective ᾱ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ᾱ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥(StatedSp 2 F))
      obtain ⟨z, rfl⟩ := hᾱ y
      exact hy ((MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top z)))
  have hcard : Nat.card (ModO2 X) = Nat.card ↥(StatedSp 2 F) :=
    Nat.card_congr (Equiv.ofBijective ᾱ ⟨hinj, hᾱ⟩)
  rw [hsp] at hcard
  rcases ht with ⟨m, -, hY⟩ | ⟨m, hm, -, hY⟩ | hY
  · rw [C48.card_psl_two_two hY] at hcard
    exact burnsideC3h_psl2_ne_sp4 hk hcard
  · rw [card_of_isSz hY] at hcard
    exact burnsideC3h_sz_ne_sp4 hm hk hcard
  · have h168 : Nat.card (ModO2 X) = 168 := by
      obtain ⟨-, F', _, _, hF', ⟨e⟩⟩ := hY
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF']
      decide
    rw [h168] at hcard
    exact burnsideC3h_168_ne_sp4 hk hcard

open CFSG.Quasithin CFSG.Quasithin.AutOn CFSG.Quasithin.C35 CFSG.LieType.BorelTits in
theorem burnsideC3h_not_isSolvable_autOn {G : Type} [Group G] [Finite G] {D K V : Subgroup G}
    (hD : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) (hDK : D ≤ K) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hC : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K) {B : Subgroup (MulAut ↥V)}
    (hDB : autOn D V ≤ B) : ¬ Group.IsSolvable ↥B := by
  intro hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥D →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion (hDK.trans hKV))
  have hψB : ∀ d : ↥D, ψ d ∈ B := fun d =>
    hDB (conjAct_mem_autOn_of_mem (hKV (hDK d.2)) d.2)
  haveI : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hD
  let ψ' : ↥D →* ↥B := ψ.codRestrict B hψB
  haveI : Group.IsPerfect ↥ψ'.range := Group.IsPerfect.range ψ'
  haveI : Group.IsSolvable ↥ψ'.range :=
    Group.isSolvable_of_isSolvable_injective (f := ψ'.range.subtype) ψ'.range.subtype_injective
  have htriv : ∀ d : ↥D, ψ' d = 1 := by
    by_contra h
    push Not at h
    obtain ⟨d, hd⟩ := h
    haveI : Nontrivial ↥ψ'.range := ⟨⟨⟨ψ' d, d, rfl⟩, 1, fun h => hd (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable ↥ψ'.range inferInstance
  have hDC : D ≤ Subgroup.centralizer (V : Set G) := fun d hd =>
    (conjAct_eq_one_iff ⟨d, hKV (hDK hd)⟩).1 (by
      have := congrArg Subtype.val (htriv ⟨d, hd⟩)
      exact this)
  exact not_isPGroup_of_perfect hD1 hD
    ((pCoreOf_isPGroup 2 K).to_le (fun d hd => hC ⟨hDK hd, hDC hd⟩))

open CFSG.QuasithinUnique CFSG.Quasithin.C35Pf in
theorem burnsideC3h_isSolvable_of_sylow_le {Γ : Type} [Group Γ] {A B S : Subgroup Γ}
    (hA : SolvOver ↥A) (hS : IsSylowTwoOf S A) (hSB : S ≤ B) (hBA : B ≤ A) (hne : B ≠ A) :
    Group.IsSolvable ↥B := by
  have hT := isSylowTwoOf_subgroupOf_top hS
  have hTB : S.subgroupOf A ≤ B.subgroupOf A := Subgroup.subgroupOf_mono A hSB
  have hne' : B.subgroupOf A ≠ ⊤ := fun h => hne (le_antisymm hBA (Subgroup.subgroupOf_eq_top.mp h))
  have := hA _ _ hT hTB hne'
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hBA).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hBA).symm.injective

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars in
open CFSG.Quasithin CFSG.Quasithin.C35 CFSG.Quasithin.C35Pf CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank in
theorem burnsideC3h_solvOver_of_levi {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (ht : burnsideC3h_LeviType Y) : SolvOver Y := by
  rcases ht with ⟨m, hm, hY⟩ | ⟨m, -, -, hY⟩ | hY
  · exact solvOver_of_isPSL2 (by omega) hY
  · exact solvOver_of_isSz hY
  · refine solvOver_of_card168 ?_
    obtain ⟨-, F', _, _, hF', ⟨e⟩⟩ := hY
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF']
    decide

open CFSG.Quasithin.C35Pf in
theorem burnsideC3h_isSolvable_of_ne_top_card60 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) {H : Subgroup X} (hH : H ≠ ⊤) : Group.IsSolvable ↥H := by
  have hd : Nat.card H ∣ 60 := hX ▸ Subgroup.card_subgroup_dvd_card H
  have h60 : Nat.card H ≠ 60 := fun h => hH (Subgroup.eq_top_of_card_eq H (by rw [h, hX]))
  have h30 : Nat.card H ≠ 30 := by
    intro h
    have hidx : H.index = 2 := by
      have := H.card_mul_index
      rw [h, hX] at this
      omega
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hb | ht
    · rw [hb] at h
      simp at h
    · exact hH ht
  have key : ∀ k : ℕ, k ∣ 60 → k ≠ 60 → k ≠ 30 →
      k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 10 ∨ k = 12 ∨ k = 15 ∨ k = 20 := by
    intro k hk h60 h30
    have : k ≤ 60 := Nat.le_of_dvd (by norm_num) hk
    interval_cases k <;> simp_all <;> omega
  rcases key _ hd h60 h30 with h | h | h | h | h | h | h | h | h | h
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 0) Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 0) Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 1) Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 0) Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 5) (a := 0) (b := 1) Nat.prime_two
      Nat.prime_five (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 5) (a := 1) (b := 1) Nat.prime_two
      Nat.prime_five (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 1) Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 3) (q := 5) (a := 1) (b := 1) Nat.prime_three
      Nat.prime_five (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (p := 2) (q := 5) (a := 2) (b := 1) Nat.prime_two
      Nat.prime_five (by norm_num) (by rw [h]; norm_num)

theorem burnsideC3h_swap_not_central {σ : Equiv.Perm (Fin 5)} (hσ : σ.IsSwap) :
    ∃ π ∈ alternatingGroup (Fin 5), σ * π * σ⁻¹ ≠ π := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  have hz : ∀ x y : Fin 5, ∃ z : Fin 5, z ≠ x ∧ z ≠ y := by decide
  obtain ⟨z, hzx, hzy⟩ := hz x y
  refine ⟨Equiv.swap x y * Equiv.swap y z, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hxy,
      Equiv.Perm.sign_swap (Ne.symm hzy |> fun h => h)]
    · decide
  · intro h
    have h2 := congrArg (fun f : Equiv.Perm (Fin 5) => f x) h
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hzx, hzy, hxy, hxy.symm, hzx.symm,
      hzy.symm] at h2

open CFSG.Quasithin.C35 in
theorem burnsideC3h_psl2_ne_const {m N : ℕ} (hN : N = 360 ∨ N = 1080 ∨ N = 6048) :
    2 ^ m * (4 ^ m - 1) ≠ N := by
  intro h
  have hle : 2 ^ m ≤ 6048 := by
    have h1 : 2 ^ m ≤ N := Nat.le_of_dvd (by omega) ⟨_, h.symm⟩
    omega
  have hm : m < 13 := by
    by_contra hm'
    have : 2 ^ 13 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m <;> rcases hN with rfl | rfl | rfl <;> norm_num at h

open CFSG.Quasithin CFSG.Quasithin.C35 in
theorem burnsideC3h_levi_card_ne {Y : Type} [Group Y] (hY : burnsideC3h_LeviType Y) {c : ℕ}
    (hc : c = 360 ∨ c = 1080 ∨ c = 6048 ∨ c = 2520 ∨ c = 20160 ∨ c = 979200 ∨ c = 9999360) :
    Nat.card Y ≠ c := by
  rcases hc with hc | hc | hc | hc | hc | hc | hc
  · rcases hY with ⟨m, -, hY⟩ | ⟨m, hm, -, hY⟩ | hY
    · rw [C48.card_psl_two_two hY]
      exact burnsideC3h_psl2_ne_const (Or.inl hc)
    · rw [card_of_isSz hY]
      intro h
      exact not_three_dvd_card_sz hm (by rw [h, hc]; norm_num)
    · obtain ⟨-, F', _, _, hF', ⟨e⟩⟩ := hY
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF', hc]
      decide
  · rcases hY with ⟨m, -, hY⟩ | ⟨m, hm, -, hY⟩ | hY
    · rw [C48.card_psl_two_two hY]
      exact burnsideC3h_psl2_ne_const (Or.inr (Or.inl hc))
    · rw [card_of_isSz hY]
      intro h
      exact not_three_dvd_card_sz hm (by rw [h, hc]; norm_num)
    · obtain ⟨-, F', _, _, hF', ⟨e⟩⟩ := hY
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF', hc]
      decide
  · rcases hY with ⟨m, -, hY⟩ | ⟨m, hm, -, hY⟩ | hY
    · rw [C48.card_psl_two_two hY]
      exact burnsideC3h_psl2_ne_const (Or.inr (Or.inr hc))
    · rw [card_of_isSz hY]
      intro h
      exact not_three_dvd_card_sz hm (by rw [h, hc]; norm_num)
    · obtain ⟨-, F', _, _, hF', ⟨e⟩⟩ := hY
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF', hc]
      decide
  all_goals exact levi_card_ne hY (by tauto)

theorem burnsideC3h_card_modO2 {G : Type} [Group G] {K : Subgroup G} {Γ : Type} [Group Γ]
    (α : ↥K →* Γ) (hs : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card Γ :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hs)).toEquiv

theorem burnsideC3h_center_eq_bot {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a)) b).symm

open CFSG.Quasithin CFSG.Quasithin.AutOn CFSG.Quasithin.C35 CFSG.LieType.BorelTits in
theorem burnsideC3h_caseB_false {G : Type} [Group G] [Finite G] {R M K D V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hCV : K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K)
    (hD : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) (hDK : D ≤ K) (hDM : D ≤ M ⊓ K)
    (α : ↥K →* alternatingGroup (Fin 5)) (hker : α.ker = CFSG.pCore 2 ↥K)
    (t : G) (htR : t ∈ R) (htV : t ∈ Subgroup.normalizer (V : Set G)) (σ : Equiv.Perm (Fin 5))
    (hσ : σ.IsSwap)
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin 5)) * σ⁻¹)
    (hMK : autOn (M ⊓ K) V =
      autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ d : ↥D, (σ * (α ⟨(d : G), hDK d.2⟩ : Equiv.Perm (Fin 5)) * σ⁻¹ =
      (α ⟨(d : G), hDK d.2⟩ : Equiv.Perm (Fin 5))) := by
    intro d
    have hd := d.2
    have hk : (d : G) ∈ K := hDK hd
    have hk' : t * (d : G) * t⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hRK htR) (d : G)).mp hk
      exact this
    have hmem : conjAct V ⟨(d : G), hKV hk⟩ ∈ autOn (M ⊓ K) V :=
      conjAct_mem_autOn_of_mem (hKV hk) (hDM hd)
    rw [hMK] at hmem
    have ht' : conjAct V ⟨t, htV⟩ ∈ autOn R V := conjAct_mem_autOn_of_mem htV htR
    have hc := Subgroup.mem_centralizer_iff.mp hmem.2 _ ht'
    have hone : conjAct V (⟨t, htV⟩ * ⟨(d : G), hKV hk⟩ * ⟨t, htV⟩⁻¹ * ⟨(d : G), hKV hk⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have hcen : t * (d : G) * t⁻¹ * (d : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have := (AutOn.conjAct_eq_one_iff _).1 hone
      simpa using this
    have hK3 : t * (d : G) * t⁻¹ * (d : G)⁻¹ ∈ K := K.mul_mem hk' (K.inv_mem hk)
    have hO : t * (d : G) * t⁻¹ * (d : G)⁻¹ ∈ pCoreOf 2 K := by
      rw [← hCV]
      exact ⟨hK3, hcen⟩
    have hker1 : (⟨t * (d : G) * t⁻¹, hk'⟩ * ⟨(d : G), hk⟩⁻¹ : ↥K) ∈ α.ker := by
      rw [hker]
      obtain ⟨y, hy, hyy⟩ := Subgroup.mem_map.mp hO
      have : y = (⟨t * (d : G) * t⁻¹, hk'⟩ * ⟨(d : G), hk⟩⁻¹ : ↥K) := Subtype.ext (by simpa using hyy)
      rwa [this] at hy
    have h1 := MonoidHom.mem_ker.mp hker1
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 := hconj (d : G) hk hk'
    rw [h1] at h2
    exact h2.symm
  let ψ : ↥D →* alternatingGroup (Fin 5) := α.comp (Subgroup.inclusion hDK)
  haveI : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hD
  haveI : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hne : ψ.range ≠ ⊤ := by
    intro htop
    obtain ⟨π, hπ, hπn⟩ := burnsideC3h_swap_not_central hσ
    obtain ⟨d, hd⟩ := (htop ▸ Subgroup.mem_top (⟨π, hπ⟩ : alternatingGroup (Fin 5)) :
      (⟨π, hπ⟩ : alternatingGroup (Fin 5)) ∈ ψ.range)
    apply hπn
    have := hcomm d
    have e : (ψ d : Equiv.Perm (Fin 5)) = π := congrArg Subtype.val hd
    rw [← e]
    exact this
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  haveI : Group.IsSolvable ↥ψ.range := burnsideC3h_isSolvable_of_ne_top_card60 h60 hne
  have htriv : ∀ d : ↥D, ψ d = 1 := by
    by_contra h
    push Not at h
    obtain ⟨d, hd⟩ := h
    haveI : Nontrivial ↥ψ.range := ⟨⟨⟨ψ d, d, rfl⟩, 1, fun h => hd (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable ↥ψ.range inferInstance
  have hDO : D ≤ pCoreOf 2 K := by
    intro d hd
    have h1 : α ⟨d, hDK hd⟩ = 1 := htriv ⟨d, hd⟩
    have h2 : (⟨d, hDK hd⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hker ▸ MonoidHom.mem_ker.mpr h1
    exact ⟨⟨d, hDK hd⟩, h2, rfl⟩
  exact not_isPGroup_of_perfect hD1 hD ((pCoreOf_isPGroup 2 K).to_le hDO)

open CFSG.Quasithin.C35 in
theorem burnsideC3h_card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars in
open CFSG.Quasithin CFSG.Quasithin.C35 CFSG.Quasithin.C35Pf CFSG.Quasithin.AutOn
  CFSG.Quasithin.SmithC27 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits in
theorem burnsideC3h_false_of_c27 {G : Type} [Group G] [Finite G] {H R M K D : Subgroup G}
    (hyp : HypC23 H R M) (hK : K ∈ cComp H) (hc : CharTwo K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hS : IsSimpleGroup (ModO2 K))
    (ht : burnsideC3h_LeviType (ModO2 K))
    (hn : ¬ K ≤ M) (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hD : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) (hDM : D ≤ M ⊓ K)
    (hconcl : C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Hyp27 H R M K := Hyp27.mk' hyp hK hq hc hn hR
  have hs := h.starHyp
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hRH : R ≤ H := hyp.radical.1
  have hRM : R ≤ M := fun x hx =>
    hyp.cgs (inf_normalizer_le_cgsIn hyp.radical.2.1 ⟨hRH hx, Subgroup.le_normalizer hx⟩)
  have hnc : ∃ a b : ModO2 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h' => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])⟩
  have hZ : Subgroup.center (ModO2 K) = ⊥ := burnsideC3h_center_eq_bot hnc
  have hCV : K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K := hs.inf_centralizer_eq hZ
  obtain ⟨e⟩ := hs.quotEquiv hZ
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hs.K_le_normalizer_V
  have hDK : D ≤ K := hDM.trans inf_le_right
  have hSolv : SolvOver ↥(autOn K V) := SolvOver.of_mulEquiv e (burnsideC3h_solvOver_of_levi ht)
  have hO2R : pCoreOf 2 K ≤ R := hs.pCore_K_le_pCore.trans hs.core
  have hproper : autOn (M ⊓ K) V ≠ autOn K V := by
    intro heq
    apply hn
    intro k hk
    have hmem : conjAct V ⟨k, hKV hk⟩ ∈ autOn (M ⊓ K) V := by
      rw [heq]
      exact conjAct_mem_autOn_of_mem (hKV hk) hk
    exact (AutOn.mem_of_conjAct_mem_autOn hKV inf_le_right
      (fun x hx => ⟨hRM (hO2R (hCV ▸ hx)), hx.1⟩) hk hmem).1
  have hD' : autOn D V ≤ autOn (M ⊓ K) V := autOn_mono hDM
  have hover : ∀ S : Subgroup (MulAut ↥V), IsSylowTwoOf S (autOn K V) →
      S ≤ autOn (M ⊓ K) V → False := fun S hS' hSB =>
    burnsideC3h_not_isSolvable_autOn hD hD1 hDK hKV (by rw [hCV]) hD'
      (burnsideC3h_isSolvable_of_sylow_le hSolv hS' hSB (autOn_mono inf_le_right) hproper)
  have hborel : CFSG.Quasithin.IsBorelIn (autOn K V) (autOn (M ⊓ K) V) → False := by
    rintro ⟨S, hS', hB⟩
    exact hover S hS' (by rw [hB]; exact le_inf hS'.1 Subgroup.le_normalizer)
  have hparab : IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) → False := by
    rintro ⟨-, S, hS', hNB⟩
    exact hover S hS' ((le_inf hS'.1 Subgroup.le_normalizer).trans hNB)
  have hcard7 : Nat.card (ModO2 K) = 2520 → False := fun hc7 =>
    burnsideC3h_levi_card_ne ht (c := 2520) (by tauto) hc7
  obtain ⟨-, -, hpart3⟩ := hconcl
  rcases hpart3 with ⟨-, (⟨-, -, hB⟩ | ⟨-, -, -, hB⟩ | ⟨hA7, -⟩ | ⟨hA7, -⟩)⟩
    | ⟨⟨n, α, hn5, hn8, -, hAlt, t, htR, htV, hRt, -, σ, hσ, hconj⟩, hMK⟩
    | ⟨hHat, -⟩ | ⟨hExc, -⟩ | ⟨-, hMP⟩ | ⟨hG2, -, -⟩ | ⟨-, hMP, -⟩ | ⟨-, hPar, -⟩
  · exact hborel hB
  · exact hborel hB
  · obtain ⟨α, hα, hk, -⟩ := hA7
    refine hcard7 ?_
    rw [burnsideC3h_card_modO2 α hα hk, burnsideC3h_card_alt 7 (by norm_num)]
    decide
  · obtain ⟨α, hα, hk, -⟩ := hA7
    refine hcard7 ?_
    rw [burnsideC3h_card_modO2 α hα hk, burnsideC3h_card_alt 7 (by norm_num)]
    decide
  · obtain ⟨hsurj, hker, -⟩ := hAlt
    have hcardn := burnsideC3h_card_modO2 α hsurj hker
    rw [burnsideC3h_card_alt n (by omega)] at hcardn
    interval_cases n
    · exact burnsideC3h_caseB_false hKV hR hCV hD hD1 hDK hDM α hker t htR htV σ hσ hconj hMK
    · exact burnsideC3h_levi_card_ne ht (c := 360) (by tauto) (by rw [hcardn]; decide)
    · exact hcard7 (by rw [hcardn]; decide)
    · exact burnsideC3h_levi_card_ne ht (c := 20160) (by tauto) (by rw [hcardn]; decide)
  · obtain ⟨-, hHatQ, -⟩ := hHat
    obtain ⟨-, hc3, ⟨e'⟩⟩ := hHatQ
    refine burnsideC3h_levi_card_ne ht (c := 1080) (by tauto) ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (ModO2 K)), hc3,
      Nat.card_congr e'.toEquiv, burnsideC3h_card_alt 6 (by norm_num)]
    decide
  · obtain ⟨-, ⟨α, hα, hk⟩, -⟩ := hExc
    refine hcard7 ?_
    rw [burnsideC3h_card_modO2 α hα hk, burnsideC3h_card_alt 7 (by norm_num)]
    decide
  · exact hparab hMP.1
  · obtain ⟨-, hU, -⟩ := hG2
    refine burnsideC3h_levi_card_ne ht (c := 6048) (by tauto) ?_
    exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hU
  · exact hparab hMP.1
  · exact hparab hPar

section BurnsideC3hCopies

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars in
open CFSG.Quasithin CFSG.Quasithin.C35 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
theorem burnsideC3h_eq_perfectCore_Y
    (hc27 : burnsideC2h_C27NoSp4 G)
    (h22one : ASC22One G) (h22two : ASC22Two G) (h22four : ASC22Four G) (hA3 : A3Orbits G)
    (hInsp : InspC35) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hHN : H ≤ Subgroup.normalizer (K : Set G)) (hb : C31Basic H R M L V K)
    (ht : C31Lie2Types (↥K ⧸ Subgroup.center ↥K)) :
    conjClosure L M = perfectCore (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) := by
  set Y := K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) with hYdef
  have hM0perf := C2Nine.perfect_conjClosure_of_hyp h
  have hM0Y : conjClosure L M ≤ Y := le_Y h hb
  have hM0X : conjClosure L M ≤ perfectCore Y := le_perfectCore_of_perfect hM0Y hM0perf
  have hM0ne : conjClosure L M ≠ ⊥ := fun h0 => h.V_ne (eq_bot_iff.mpr (h0 ▸ h.V_le))
  have hXne : perfectCore Y ≠ ⊥ := fun h0 => hM0ne (eq_bot_iff.mpr (h0 ▸ hM0X))
  have hXperf : ⁅perfectCore Y, perfectCore Y⁆ = perfectCore Y := perfectCore_perfect Y
  obtain ⟨hchar, htypes, hL4⟩ := hInsp.levi G K Y hK.2.2 hb.2.2 ht
    (isParabolic2_Y h22four h hK hHN hb ht) (Y_ne h22two h hK hb) hXne
  have hS : IsSimpleGroup (ModO2 (perfectCore Y)) := by
    rcases htypes with ⟨m, -, hm⟩ | ⟨m, -, -, hm⟩ | hm | hm
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m hm).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 m hm).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hm).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 hm).2
  have hnormal : perfectCore Y ≤ Subgroup.normalizer (conjClosure L M : Set G) →
      conjClosure L M = perfectCore Y :=
    fun hXN => eq_of_le_normalizer hM0X hXN hM0perf hM0ne hXperf hS
  by_cases h4 : IsPSL 4 2 1 (ModO2 (perfectCore Y))
  ·
    obtain ⟨-, -, hinn⟩ := hL4 h4
    apply hnormal
    have hYR := le_normalizer_R_of_inner h22one h hK hHN hb hinn
    have hYM : Y ≤ M := (le_inf (inf_le_left.trans hK.1) hYR).trans (C2Nine.inf_normalizer_le_M h)
    exact (perfectCore_le Y).trans (hYM.trans (le_normalizer_conjClosure L M))
  ·
    by_contra hne
    have htypes' : (∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m (ModO2 (perfectCore Y))) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m (ModO2 (perfectCore Y))) ∨
        IsPSL 3 2 1 (ModO2 (perfectCore Y)) := by
      rcases htypes with h1 | h2 | h3 | h4'
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
      · exact absurd h4' h4
    obtain ⟨T, hT, hRT⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge h.le_M h.pgroup
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.1.trans hb.2.1
    have hTX : T ≤ Subgroup.normalizer (perfectCore Y : Set G) :=
      (le_normalizer_Y hTK (T_le_normalizer_R h hT hRT)).trans
        (normalizer_le_normalizer_perfectCore Y)
    have hX'H : perfectCore Y ⊔ T ≤ H :=
      sup_le ((perfectCore_le Y).trans (inf_le_left.trans hK.1)) (hT.1.trans h.le_H)
    have h' := c2_9_three hA3 h hT hRT (sup_le_sup_right hM0X T) hX'H
    have hXc : perfectCore Y ∈ cComp (perfectCore Y ⊔ T) :=
      mem_cComp_sup (mem_cComp_self_of_simple hXne hXperf hS) hTX
    have hXM : ¬ perfectCore Y ≤ M ⊓ (perfectCore Y ⊔ T) := fun hle =>
      hne (hnormal ((hle.trans inf_le_left).trans (le_normalizer_conjClosure L M)))

    have hSp : CFSG.Quasithin.MS93.MRes.NoSp4Quot (perfectCore Y) :=
      burnsideC3h_noSp4Quot_of_levi hS htypes'
    have hconcl := hc27 (perfectCore Y ⊔ T) R (M ⊓ (perfectCore Y ⊔ T)) (perfectCore Y) _
      (c2_10_four h') hXc (isQuasisimple_modO2 hXperf hS) hchar hXM (hRT.trans hTX) rfl hSp
    exact burnsideC3h_false_of_c27 (c2_10_four h') hXc hchar
      (isQuasisimple_modO2 hXperf hS) hS htypes' hXM (hRT.trans hTX) hM0perf hM0ne
      (le_inf (le_inf (C2Nine.conjClosure_le_M h) (hM0X.trans le_sup_left)) hM0X) hconcl

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars in
open CFSG.Quasithin CFSG.Quasithin.C35 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
theorem burnsideC3h_c31LieStep_of (hInsp : InspC35)
    (hc27 : burnsideC2h_C27NoSp4 G)
    (h22one : ASC22One G) (h22two : ASC22Two G) (h22four : ASC22Four G) (hA3 : A3Orbits G)
    (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hInsp33 : InspC33) (hSp4 : SchurMult2Sp4) (hL42 : SchurMult2L42) (hL52 : SchurMult2L52) :
    C31LieStep G := by
  intro H R M L V K h hK hb ht
  have hHN := C31B.le_normalizer h36 h38 hA3 hSch hInsp33 h hK
  have hM0 := burnsideC3h_eq_perfectCore_Y hc27 h22one h22two h22four hA3 hInsp h hK hHN hb ht
  have hD := c35Data_of h22two h22four h hK hHN hb ht hM0
  have hYM := Y_le_M hC129 hC111 hC19 hA3 h hK inf_le_left hM0
  have hKM : ¬ K ≤ M := c2_10_two h K hK
  have hZ := isPGroup_center hb.2.2
  have hsmall := hInsp.small G _ _ _ _ hD
  have hc1 : C35Concl1 K (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G))
      (conjClosure L M) V → L = conjClosure L M ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K) := fun h1 => by
    obtain ⟨n, -, -, hpsl, -⟩ := id h1
    exact ⟨eq_conjClosure_of_modO2 hA3 h
        (C31Spor.quasiNoTwo_of_isPSL hpsl (not_prime_card_psl22 hpsl)),
      Or.inl (c31Case1_of hSp4 hK hb.2.2 hYM hKM hM0 h1)⟩
  have hc45 : (IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K)) → L = conjClosure L M ∧
      (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case10 H R M L V K) := by
    intro h45
    by_cases hZb : Subgroup.center ↥K = ⊥
    · rcases hInsp.l45 G _ _ _ _ hD hZb h45 with ⟨n, hn, h2a⟩ | h2b
      · refine ⟨eq_conjClosure_of_modO2 hA3 h ?_,
          Or.inr (Or.inl (c31Case2_of_concl2a hn hYM hKM hM0 h2a))⟩
        rcases hn with rfl | rfl
        · exact C31Spor.quasiNoTwo_L32 h2a.2.2.1
        · exact C31Spor.quasiNoTwo_L42 h2a.2.2.1
      · exact ⟨C31Spor.eq_conjClosure_of_isExt hA3 h (fun h => C48Spor.isPGroup_of_isE2 h)
          (fun h => C31Spor.quasiNoTwo_L32 h) h2b.2.1,
          Or.inr (Or.inl (c31Case2_of_concl2b hYM hD.parabolic hKM h2b))⟩
    · have h4 : IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) := by
        rcases h45 with h4 | h8 | h5
        · exact h4
        · exact isPSL_four_two_of_isAlt_eight h8
        · exact absurd (hL52 ↥K hK.2.2 hZ h5) hZb
      have hc2 : Nat.card ↥(Subgroup.center ↥K) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (hL42 ↥K hK.2.2 hZ h4) with h1 | h2
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZb
        · exact h2
      have h10 := hInsp.a8cover G _ _ _ _ hD hc2 (Or.inl h4)
      exact ⟨eq_conjClosure_of_isB48TwoModule hA3 h h10.2.2,
        Or.inr (Or.inr ⟨h10.1, h10.2.1, h10.2.2⟩)⟩
  unfold C31Lie2Types at ht
  rcases ht with h5 | h6 | h8 | (⟨f, ⟨hf, h2⟩ | ⟨hf, h3⟩ | ⟨hf, hu⟩ | ⟨hf, hsp⟩ | ⟨hf, hg⟩ |
      ⟨hf, hd⟩ | ⟨hfo, hf3, hf4⟩ | ⟨hfo, hf3, hsz⟩⟩ | htits) | ⟨n, hn, hpsl⟩
  · exact (hsmall (Or.inr (Or.inl h5))).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inl h6)))).elim
  · exact hc45 (Or.inr (Or.inl h8))
  · exact (hsmall (Or.inl ⟨f, Or.inl ⟨hf, h2⟩⟩)).elim
  · rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inl h3))))).elim
    · exact hc1 (hInsp.l3 G _ _ _ _ hD f hf2 h3)
  · exact (hsmall (Or.inl ⟨f, Or.inr (Or.inl ⟨hf, hu⟩)⟩)).elim
  · exact hc1 (hInsp.sp4 G _ _ _ _ hD f hf hsp)
  · exact hc1 (hInsp.g2 G _ _ _ _ hD f hf hg)
  · exact hc1 (hInsp.d4 G _ _ _ _ hD f hf hd)
  · exact hc1 (hInsp.f4 G _ _ _ _ hD f hfo hf3 hf4)
  · exact (hsmall (Or.inl ⟨f, Or.inr (Or.inr ⟨hfo, hf3, hsz⟩)⟩)).elim
  · exact (hsmall (Or.inr (Or.inr (Or.inr (Or.inr htits))))).elim
  · rcases hn with rfl | rfl
    · exact hc45 (Or.inl hpsl)
    · exact hc45 (Or.inr (Or.inr hpsl))

end BurnsideC3hCopies

section

theorem as_C_3_5
    : C_3_5 := by
  intro G _ _ H R M L V T K hS hLK hKT hLie
  have hA37 := CFSG.Quasithin.H13.a3ForSQTK_holds.1
  have hA38 := CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  have hA3 : CFSG.Quasithin.A3Orbits G := CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38
  have hSch : ∀ K : Subgroup G, CFSG.Quasithin.IsSQTKIn K →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      CFSG.Quasithin.OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
    fun K hK hq => CFSG.Quasithin.C41Pf.outSolvable_of_isSQTKIn K hK hq
  have hbasic := CFSG.Quasithin.C31B.c31BasicStep_of CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
    hA38 hA3 hSch CFSG.Quasithin.H13.InspC33P.inspC33_holds H R M L V K hS.hyp hS.comp
  have hSQT := burnsideC3h_pRank_of_isComponentOf hS.hyp.sqtk hS.comp
  have hLie2 : CFSG.Quasithin.C31Lie2Types (↥K ⧸ Subgroup.center ↥K) := by
    rcases hLie with hE | h6 | hU
    · exact burnsideC3h_lie2Types_of_evenLieType hSQT hE
    · exact Or.inr (Or.inl h6)
    · exact absurd (Or.inr ⟨3, Nat.prime_three, by norm_num, Or.inr (Or.inr hU)⟩)
        (CFSG.Quasithin.C31NL.c31NonLieStep_holds H R M L V K hS.hyp hS.comp hbasic)
  have h22 : CFSG.Quasithin.ASC22Statement G := CFSG.Quasithin.C22Pf.asc22Statement_holds hA37
  exact (burnsideC3h_c31LieStep_of CFSG.Quasithin.C35Pf.inspC35_holds
    (burnsideC2h_c27_of_noSp4Quot G) h22.1 h22.2.1 h22.2.2.2 hA3
    (CFSG.Quasithin.H13.VolI.asc129Statement_holds G) (CFSG.Quasithin.asc111Statement_holds G)
    (CFSG.Quasithin.asc19Statement_holds G) CFSG.Quasithin.H13.VolI.a36ForSQTK_holds hA38 hSch
    CFSG.Quasithin.H13.InspC33P.inspC33_holds CFSG.Quasithin.schurMult2Sp4_holds
    CFSG.Quasithin.schurMult2L42_holds CFSG.Quasithin.schurMult2L52_holds
    H R M L V K hS.hyp hS.comp hbasic hLie2).2

end

end CFSG.ASVolI
