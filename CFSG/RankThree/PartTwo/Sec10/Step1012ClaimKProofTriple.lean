module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.Native.ONTripleSylow

public section

namespace CFSG.RankThree.PartTwo.Sec10

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Step1012ClaimKProof

section General

variable {Q : Type} [Group Q]

theorem conj_eq_one_iff {g : Q} : MulAut.conj g = 1 ↔ g ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h1 := congrArg (fun φ : MulAut Q => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← h x, mul_inv_cancel_right]

theorem fix_center_of_pow_three [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3)
    {f : MulAut Q} (hf : f ^ 3 = 1) {z : Q} (hz : z ∈ Subgroup.center Q) : f z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfz : f z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := f.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨z, hz⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZz : Subgroup.center Q = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    rw [hZ, Nat.card_zpowers, hzo]
  rw [hZz] at hfz
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr hfz
  replace hk : z ^ k = f z := hk
  have hfz' : f z = z ^ (k % 3) := by rw [← hzo, pow_mod_orderOf, hk]
  have hcube : f (f (f z)) = z := by
    have h := congrArg (fun φ : MulAut Q => φ z) hf
    simpa [pow_succ, MulAut.mul_apply] using h
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [hr, pow_zero] at hfz'
    exact absurd (f.injective (hfz'.trans (map_one f).symm)) hz1
  · rwa [hr, pow_one] at hfz'
  · rw [hr] at hfz'
    exfalso
    apply hz1
    have h2 : f (f z) = z := by
      rw [hfz', map_pow, hfz', ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz3,
        one_mul, pow_one]
    rw [h2, hfz', sq] at hcube
    exact mul_left_cancel (hcube.trans (mul_one z).symm)

theorem card_map_conj [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3) {H : Subgroup Q}
    (hH : Subgroup.center Q ≤ H) :
    Nat.card (H.map (MulAut.conj : Q →* MulAut Q)) * 3 = Nat.card H := by
  set φ := (MulAut.conj : Q →* MulAut Q).domRestrict H with hφ
  have hrange : φ.range = H.map (MulAut.conj : Q →* MulAut Q) := MonoidHom.domRestrict_range _ _
  have hkerEq : φ.ker = (Subgroup.center Q).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact conj_eq_one_iff
  have hker : Nat.card φ.ker = 3 := by
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hZ]
  rw [← hrange, ← Subgroup.index_ker, ← hker, mul_comm, Subgroup.card_mul_index]

@[expose] def commHom (g : Q) (H : Subgroup Q) (hc : ∀ u ∈ H, ⁅g, u⁆ ∈ Subgroup.center Q) :
    H →* Q where
  toFun u := ⁅g, (u : Q)⁆
  map_one' := by simp
  map_mul' u v := by
    have hv := Subgroup.mem_center_iff.mp (hc v v.2)
    simp only [commutatorElement_def] at hv
    simp only [Subgroup.coe_mul, commutatorElement_def]
    have key : g * ((u : Q) * v) * g⁻¹ * ((u : Q) * v)⁻¹ =
        g * u * g⁻¹ * ((g * v * g⁻¹ * (v : Q)⁻¹) * (u : Q)⁻¹) := by group
    rw [key, ← hv (u : Q)⁻¹]
    group

theorem commHom_apply_eq_one_iff (g : Q) (H : Subgroup Q)
    (hc : ∀ u ∈ H, ⁅g, u⁆ ∈ Subgroup.center Q) (u : H) :
    commHom g H hc u = 1 ↔ g * u = u * g :=
  commutatorElement_eq_one_iff_mul_comm

end General

section Model

variable {Q : Type} [Group Q]

private theorem exists_twoGroup
    [Finite Q] (ψ : Q ≃* Native.ONTriple.GM) :
    ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card Q := by
    rw [Nat.card_congr ψ.toEquiv, Native.ONTriple.card_GM]
    norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨Subgroup.zpowers t, ?_, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht,
    pow_one])⟩
  intro hb
  rw [Subgroup.zpowers_eq_bot] at hb
  rw [hb, orderOf_one] at ht
  norm_num at ht

private theorem exists_twoGroup_of_isE27
    (ψ : Q ≃* Native.ONTriple.GM) {E : Subgroup Q}
    (hE : Late.IsE27 E) :
    ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' := E.map ψ.toMonoidHom with hE'
  have hE'27 : Late.IsE27 E' := Sec13.ON134.isE27_map hE ψ.toMonoidHom ψ.injective
  obtain ⟨S, hS⟩ :=
    maxInvariantPiSubgroups_nonempty (⊤ : Subgroup Native.ONTriple.GM) E' (piOf 2)
  have hzcard : Nat.card (Subgroup.zpowers Native.ONTriple.zG) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) Native.ONTriple.relG.xcube
  obtain ⟨y, hyE, hyz⟩ : ∃ y ∈ E', y ∉ Subgroup.zpowers Native.ONTriple.zG := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show E' ≤ Subgroup.zpowers Native.ONTriple.zG from hall)
    rw [hE'27.2] at h1
    omega
  obtain ⟨hK4, -⟩ := Native.ONTriple.part_three_M hE'27 hyE hyz hS
  obtain ⟨⟨-, hS2, hSE⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hS
  have hS2' : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS2
  refine ⟨S.map ψ.symm.toMonoidHom, ?_, hS2'.map _, ?_⟩
  · intro hb
    rw [Subgroup.map_eq_bot_iff_of_injective _ ψ.symm.injective] at hb
    have h4 := hK4.card_four
    rw [hb, Subgroup.card_bot] at h4
    norm_num at h4
  · have hEE : E = E'.map ψ.symm.toMonoidHom := by
      ext x
      simp [hE']
    rw [← Subgroup.map_equiv_normalizer_eq, hEE]
    exact Subgroup.map_mono hSE

private theorem pow_three_of_conj
    (ψ : Q ≃* Native.ONTriple.GM)
    (hZ : Nat.card (Subgroup.center Q) = 3) {g : Q} (hg : MulAut.conj g ^ 3 = 1) :
    g ^ 3 = 1 := by
  have h1 : g ^ 3 ∈ Subgroup.center Q := conj_eq_one_iff.mp (by rw [map_pow]; exact hg)
  have h2 : (g ^ 3) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨g ^ 3, h1⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  exact Sec13.ON134.pow_three_eq_one ψ (k := 2)
    (by rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]; exact h2)

private theorem isE27_of_commute
    [Finite Q] (ψ : Q ≃* Native.ONTriple.GM)
    (hZ : Nat.card (Subgroup.center Q) = 3) {g x : Q} (hg3 : g ^ 3 = 1)
    (hgZ : g ∉ Subgroup.center Q) (hx3 : x ^ 3 = 1) (hxg : x * g = g * x)
    (hxY : x ∉ Subgroup.zpowers g ⊔ Subgroup.center Q) :
    Late.IsE27 (Subgroup.zpowers x ⊔ (Subgroup.zpowers g ⊔ Subgroup.center Q)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 3 (by rw [hZ])
  have hz₀o : orderOf (z₀ : Q) = 3 := by rwa [Subgroup.orderOf_coe]
  have hZz : Subgroup.center Q = Subgroup.zpowers (z₀ : Q) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z₀.2)
    rw [hZ, Nat.card_zpowers, hz₀o]
  set Y := Subgroup.zpowers g ⊔ Subgroup.center Q with hY
  have hY9 : Nat.card Y = 9 := by
    rw [hY, hZz, sup_comm]
    refine Sec4.card_zpowers_sup_zpowers hg3 hz₀o (fun h => hgZ (hZz ▸ h)) ?_
    exact (Subgroup.mem_center_iff.mp z₀.2 g)
  have hY3 : ∀ s ∈ Y, s ^ 3 = 1 := by
    intro s hs
    have h := pow_card_eq_one' (G := Y) (x := ⟨s, hs⟩)
    rw [hY9] at h
    exact Sec13.ON134.pow_three_eq_one ψ (k := 2) (by simpa using congrArg Subtype.val h)
  have hxC : Y ≤ Subgroup.centralizer ({x} : Set Q) := by
    refine sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hxg.symm)) ?_
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hw x).symm
  exact Sec13.isElemAbelian_zpowers_sup_of_card_nine hx3 hxY le_rfl hY9 hY3
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hxC hy)).symm

theorem exists_invariant_of_isTripleCover_ON
    [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (hON : Sec4.IsTripleCover Q Blueprint.NativeSporadic.ON) {F : Subgroup (MulAut Q)}
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (h27 : Nat.card F ≤ 27) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧
      ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hq.1 hON
  have hZ : Nat.card (Subgroup.center Q) = 3 := hON.1
  have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  have hinner : ∀ f ∈ F, ∃ g : Q, MulAut.conj g = f := by
    intro f hf
    obtain ⟨g, hg⟩ := Sec13.ON134.aut_inner ψ f
      (fun z hz => fix_center_of_pow_three hZ (hF.2 f hf) hz)
    exact ⟨g, by ext x; rw [MulAut.conj_apply, hg x]⟩
  have hexists : 1 < Nat.card F → ∃ f ∈ F, f ≠ 1 := fun h1 => by
    obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      ((Subgroup.one_lt_card_iff_ne_bot F).mp h1)
    exact ⟨f, hf, fun h => hf1 (Subtype.ext h)⟩
  obtain ⟨n, hn⟩ := hF3.exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h81 : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at h81
    omega
  interval_cases n
  ·
    obtain ⟨V, hV1, hV2⟩ := exists_twoGroup ψ
    refine ⟨⊥, bot_le, by rw [hn, Subgroup.card_bot]; norm_num, V, hV1, hV2, ?_⟩
    intro f hf v hv
    rw [Subgroup.mem_bot.mp hf]
    exact hv
  ·
    obtain ⟨V, hV1, hV2⟩ := exists_twoGroup ψ
    refine ⟨⊥, bot_le, by rw [hn, Subgroup.card_bot]; norm_num, V, hV1, hV2, ?_⟩
    intro f hf v hv
    rw [Subgroup.mem_bot.mp hf]
    exact hv
  ·
    obtain ⟨f, hfF, hf1⟩ := hexists (by rw [hn]; norm_num)
    obtain ⟨g, rfl⟩ := hinner f hfF
    have hg3 : g ^ 3 = 1 := pow_three_of_conj ψ hZ (hF.2 _ hfF)
    have hgZ : g ∉ Subgroup.center Q := fun h => hf1 (conj_eq_one_iff.mpr h)
    obtain ⟨x, hx3, hxg, hxY⟩ := Sec13.ON134.exists_centralizer ψ hg3 hgZ
    have hE := isE27_of_commute ψ hZ hg3 hgZ hx3 hxg hxY
    obtain ⟨V, hV1, hV2, hEV⟩ := exists_twoGroup_of_isE27 ψ hE
    refine ⟨Subgroup.zpowers (MulAut.conj g), Subgroup.zpowers_le.mpr hfF, ?_, V, hV1, hV2, ?_⟩
    · rw [hn, Nat.card_zpowers, orderOf_eq_prime (hF.2 _ hfF) hf1]
      norm_num
    · intro f' hf' v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf'
      rw [← map_zpow, MulAut.conj_apply]
      have hgk : g ^ k ∈ Subgroup.zpowers x ⊔ (Subgroup.zpowers g ⊔ Subgroup.center Q) :=
        Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers g k))
      exact (Subgroup.mem_normalizer_iff.mp (hEV hgk) v).mp hv
  ·
    obtain ⟨f₁, hf₁F, hf₁1⟩ := hexists (by rw [hn]; norm_num)
    obtain ⟨g₁, rfl⟩ := hinner f₁ hf₁F
    have hg₁3 : g₁ ^ 3 = 1 := pow_three_of_conj ψ hZ (hF.2 _ hf₁F)
    have hg₁Z : g₁ ∉ Subgroup.center Q := fun h => hf₁1 (conj_eq_one_iff.mpr h)
    have hf₁o : orderOf (MulAut.conj g₁) = 3 := orderOf_eq_prime (hF.2 _ hf₁F) hf₁1
    set Ft := F.comap (MulAut.conj : Q →* MulAut Q) with hFt
    have hZFt : Subgroup.center Q ≤ Ft := fun z hz => by
      rw [Subgroup.mem_comap, conj_eq_one_iff.mpr hz]
      exact F.one_mem
    have hFtmap : Ft.map (MulAut.conj : Q →* MulAut Q) = F := by
      rw [hFt, Subgroup.map_comap_eq, inf_eq_right]
      intro f hf
      obtain ⟨g, rfl⟩ := hinner f hf
      exact ⟨g, rfl⟩
    have hFtcard : Nat.card Ft = 81 := by
      have h1 := card_map_conj hZ hZFt
      rw [hFtmap, hn] at h1
      omega
    have hcomm : ∀ u ∈ Ft, ⁅g₁, u⁆ ∈ Subgroup.center Q := by
      intro u hu
      apply conj_eq_one_iff.mp
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hF.1.is_comm.comm ⟨_, hf₁F⟩ ⟨_, hu⟩)
    set φ := commHom g₁ Ft hcomm with hφ
    have hrange : φ.range ≤ Subgroup.center Q := by
      rintro _ ⟨u, rfl⟩
      exact hcomm u u.2
    have hker : 27 ≤ Nat.card φ.ker := by
      have h1 := Subgroup.card_mul_index φ.ker
      rw [Subgroup.index_ker, hFtcard] at h1
      have h2 : Nat.card φ.range ≤ 3 := hZ ▸ Subgroup.card_le_of_le hrange
      have h3 : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
        Nat.mul_le_mul_left _ h2
      omega
    set C := φ.ker.map Ft.subtype with hC
    have hCcard : Nat.card C = Nat.card φ.ker :=
      Subgroup.card_map_of_injective Ft.subtype_injective
    have hZC : Subgroup.center Q ≤ C := by
      intro z hz
      refine ⟨⟨z, hZFt hz⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ, commHom_apply_eq_one_iff]
      exact Subgroup.mem_center_iff.mp hz g₁
    have hCmap : 9 ≤ Nat.card (C.map (MulAut.conj : Q →* MulAut Q)) := by
      have h1 := card_map_conj hZ hZC
      omega
    obtain ⟨f₂, hf₂C, hf₂⟩ : ∃ f₂ ∈ C.map (MulAut.conj : Q →* MulAut Q),
        f₂ ∉ Subgroup.zpowers (MulAut.conj g₁) := by
      by_contra hall
      push Not at hall
      have h1 := Subgroup.card_le_of_le
        (show C.map (MulAut.conj : Q →* MulAut Q) ≤ Subgroup.zpowers (MulAut.conj g₁) from hall)
      rw [Nat.card_zpowers, hf₁o] at h1
      omega
    obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hf₂C
    set g₂ : Q := (u : Q) with hg₂
    have hg₂F : MulAut.conj g₂ ∈ F := u.2
    have hg₂g₁ : g₂ * g₁ = g₁ * g₂ := ((commHom_apply_eq_one_iff g₁ Ft hcomm u).mp hu).symm
    have hg₂3 : g₂ ^ 3 = 1 := pow_three_of_conj ψ hZ (hF.2 _ hg₂F)
    have hg₂Y : g₂ ∉ Subgroup.zpowers g₁ ⊔ Subgroup.center Q := by
      intro hmem
      apply hf₂
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj : Q →* MulAut Q) hmem
      rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
      have h2 : (Subgroup.center Q).map (MulAut.conj : Q →* MulAut Q) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro z hz
        exact conj_eq_one_iff.mpr hz
      rwa [h2, sup_bot_eq] at h1
    set E := Subgroup.zpowers g₂ ⊔ (Subgroup.zpowers g₁ ⊔ Subgroup.center Q) with hE
    have hE27 : Late.IsE27 E := isE27_of_commute ψ hZ hg₁3 hg₁Z hg₂3 hg₂g₁ hg₂Y
    have hEFt : E ≤ Ft :=
      sup_le (Subgroup.zpowers_le.mpr hg₂F)
        (sup_le (Subgroup.zpowers_le.mpr hf₁F) hZFt)
    have hZE : Subgroup.center Q ≤ E := le_sup_right.trans le_sup_right
    obtain ⟨V, hV1, hV2, hEV⟩ := exists_twoGroup_of_isE27 ψ hE27
    refine ⟨E.map (MulAut.conj : Q →* MulAut Q), ?_, ?_, V, hV1, hV2, ?_⟩
    · rw [← hFtmap]
      exact Subgroup.map_mono hEFt
    · have h1 := card_map_conj hZ hZE
      rw [hE27.2] at h1
      rw [hn]
      omega
    · rintro _ ⟨e, he, rfl⟩ v hv
      rw [MulAut.conj_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hEV he) v).mp hv

end Model

end Step1012ClaimKProof

end CFSG.RankThree.PartTwo.Sec10
