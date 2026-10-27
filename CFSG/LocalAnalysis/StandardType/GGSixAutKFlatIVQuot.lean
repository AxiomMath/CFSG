module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section CentralSurjection

variable {A B : Type*} [Group A] [Group B]

theorem ggMem_center_of_map_mem_center (Φ : A →* B) (hΦ : Function.Surjective Φ)
    (hker : ∀ a : A, Φ a = 1 → a ∈ Subgroup.center A) (hA : commutator A = ⊤) {a : A}
    (ha : Φ a ∈ Subgroup.center B) : a ∈ Subgroup.center A := by
  have hcentral : ∀ x : A, ⁅a, x⁆ ∈ Subgroup.center A := by
    intro x
    apply hker
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp ha (Φ x)).symm
  have hmul : ∀ x y : A, ⁅a, x * y⁆ = ⁅a, x⁆ * ⁅a, y⁆ := by
    intro x y
    have hcx : Commute x ⁅a, y⁆ := Subgroup.mem_center_iff.mp (hcentral y) x
    have hconj : x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ := by
      rw [hcx.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [commutatorElement_mul_right_eq_mul_conj]
    conv_rhs => rw [← hconj]
    group
  let f : A →* A := MonoidHom.mk' (fun x => ⁅a, x⁆) hmul
  have hfrange : f.range ≤ Subgroup.center A := by
    rintro y ⟨x, rfl⟩
    exact hcentral x
  have hfrbot : f.range = ⊥ := by
    have h1 : f.range = ⁅f.range, f.range⁆ := by
      have h2 := map_commutator_eq (G := A) f
      rw [hA, Subgroup.map_top] at h2
      exact h2
    rw [h1]
    exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono hfrange hfrange)
      (le_of_eq (Subgroup.commutator_center_right (Subgroup.center A))))
  rw [Subgroup.mem_center_iff]
  intro g
  have hfg : f g = 1 := by
    have : f g ∈ f.range := ⟨g, rfl⟩
    rw [hfrbot] at this
    exact Subgroup.mem_bot.mp this
  have hfg' : ⁅a, g⁆ = 1 := hfg
  exact (commutatorElement_eq_one_iff_mul_comm.mp hfg').symm

theorem ggCenterQuotEquiv (Φ : A →* B) (hΦ : Function.Surjective Φ)
    (hker : ∀ a : A, Φ a = 1 → a ∈ Subgroup.center A) (hA : commutator A = ⊤) :
    Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) := by
  let Φ' : A →* B ⧸ Subgroup.center B :=
    (QuotientGroup.mk' (Subgroup.center B)).comp Φ
  have hΦ' : Function.Surjective Φ' :=
    (QuotientGroup.mk'_surjective (Subgroup.center B)).comp hΦ
  have hker' : Φ'.ker = Subgroup.center A := by
    ext a
    simp only [MonoidHom.mem_ker, Φ', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨fun ha => ggMem_center_of_map_mem_center Φ hΦ hker hA ha,
      fun ha => Subgroup.map_center_le_center (f := Φ) hΦ ⟨a, ha, rfl⟩⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker').symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ' hΦ')⟩

theorem ggQuasisimple_of_central_surjective (Φ : A →* B) (hΦ : Function.Surjective Φ)
    (hker : ∀ a : A, Φ a = 1 → a ∈ Subgroup.center A) (hA : CFSG.Assembly.IsQuasisimple A) :
    CFSG.Assembly.IsQuasisimple B := by
  have hperfA : commutator A = ⊤ := hA.1
  obtain ⟨e⟩ := ggCenterQuotEquiv Φ hΦ hker hperfA
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := hA.2
  refine ⟨?_, e.symm.isSimpleGroup⟩
  have h1 : (commutator A).map Φ = commutator B := by
    rw [map_commutator_eq (G := A) Φ, MonoidHom.range_eq_top.mpr hΦ]
    rfl
  rw [← h1, hperfA, Subgroup.map_top, MonoidHom.range_eq_top.mpr hΦ]

theorem ggLargeEvenMarking_of_centerQuot_equiv (hB : commutator B = ⊤)
    (e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B)
    (h : LargeEvenMarking A (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking B (fun _ _ _ _ _ _ => True) := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hB, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, -⟩
  exact ⟨hs, hna, e.symm.trans θ, trivial⟩

theorem ggQuasisimple_marking_of_central_surjective (Φ : A →* B)
    (hΦ : Function.Surjective Φ) (hker : ∀ a : A, Φ a = 1 → a ∈ Subgroup.center A)
    (hA : CFSG.Assembly.IsQuasisimple A) (h : LargeEvenMarking A (fun _ _ _ _ _ _ => True)) :
    CFSG.Assembly.IsQuasisimple B ∧ LargeEvenMarking B (fun _ _ _ _ _ _ => True) := by
  have hB := ggQuasisimple_of_central_surjective Φ hΦ hker hA
  obtain ⟨e⟩ := ggCenterQuotEquiv Φ hΦ hker hA.1
  exact ⟨hB, ggLargeEvenMarking_of_centerQuot_equiv hB.1 e h⟩

end CentralSurjection

section SimpleQuotient

theorem ggQuasisimple_centerQuot {D : Type*} [Group D] (hD : CFSG.Assembly.IsQuasisimple D) :
    IsSimpleGroup (D ⧸ Subgroup.center D) ∧
      ∃ a b : D ⧸ Subgroup.center D, a * b ≠ b * a := by
  haveI : IsSimpleGroup (D ⧸ Subgroup.center D) := hD.2
  refine ⟨hD.2, ?_⟩
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative (D ⧸ Subgroup.center D) := ⟨⟨fun a b => hcon a b⟩⟩
  have hle : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    have h := map_commutatorElement (QuotientGroup.mk' (Subgroup.center D)) x y
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcon _ _)] at h
    exact h
  rw [hD.1, top_le_iff] at hle
  have htriv : Subsingleton (D ⧸ Subgroup.center D) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [QuotientGroup.eq]
        rw [hle]
        exact Subgroup.mem_top _
  exact (not_subsingleton _) htriv

theorem ggLargeEvenMarking_of_simple_quotient {S D : Type*} [Group S] [Group D]
    (hD : CFSG.Assembly.IsQuasisimple D) (κ : S →* D ⧸ Subgroup.center D)
    (hκ : Function.Surjective κ)
    (h : LargeEvenMarking (S ⧸ κ.ker) (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking D (fun _ _ _ _ _ _ => True) := by
  obtain ⟨hDq, hna⟩ := ggQuasisimple_centerQuot hD
  let ε : S ⧸ κ.ker ≃* D ⧸ Subgroup.center D :=
    QuotientGroup.quotientKerEquivOfSurjective κ hκ
  haveI : IsSimpleGroup (D ⧸ Subgroup.center D) := hDq
  haveI : IsSimpleGroup (S ⧸ κ.ker) := ε.isSimpleGroup
  have hcenter : Subgroup.center (S ⧸ κ.ker) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (H := Subgroup.center (S ⧸ κ.ker)) with hbot | htop
    · exact hbot
    · exfalso
      haveI : IsMulCommutative (S ⧸ κ.ker) := Subgroup.center_eq_top_iff.mp htop
      obtain ⟨a, b, hab⟩ := hna
      refine hab ?_
      have h' := congrArg ε (mul_comm' (ε.symm a) (ε.symm b))
      simpa using h'
  let e : (S ⧸ κ.ker) ⧸ Subgroup.center (S ⧸ κ.ker) ≃* D ⧸ Subgroup.center D :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans ε
  exact ggLargeEvenMarking_of_centerQuot_equiv hD.1 e h

theorem ggNormalPGroup_le_ker {S D' : Type*} [Group S] [Group D'] [Finite D'] (κ : S →* D')
    (hκ : Function.Surjective κ) (hD' : IsSimpleGroup D') (hnc : ∃ a b : D', a * b ≠ b * a)
    (T : Subgroup S) [T.Normal] (hT : IsPGroup 2 T) : T ≤ κ.ker := by
  haveI : IsSimpleGroup D' := hD'
  have hmap : IsPGroup 2 (T.map κ) := hT.map κ
  haveI hnormal : (T.map κ).Normal := Subgroup.Normal.map (H := T) inferInstance κ hκ
  rcases Subgroup.Normal.eq_bot_or_eq_top (H := T.map κ) with hbot | htop
  · exact (Subgroup.map_eq_bot_iff (H := T) (f := κ)).mp hbot
  · exfalso
    have htop2 : IsPGroup 2 (⊤ : Subgroup D') := htop ▸ hmap
    have hD'2 : IsPGroup 2 D' := htop2.of_equiv Subgroup.topEquiv
    haveI hnil : Group.IsNilpotent D' := hD'2.isNilpotent
    have hsol : Group.IsSolvable D' := inferInstance
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b)

end SimpleQuotient

section Chains

variable {X W' : Type*} [Group X] [Group W']

theorem ggExists_central_surj {W : Subgroup X} (π : ↥W →* W') {C₀ : Subgroup X} (hC₀W : C₀ ≤ W)
    {C : Subgroup W'} (hC : (C₀.subgroupOf W).map π = C)
    (hker : ∀ w : ↥W, π w = 1 → (w : X) ∈ Subgroup.centralizer (C₀ : Set X)) :
    ∃ Φ : ↥C₀ →* ↥C, Function.Surjective Φ ∧ ∀ a : ↥C₀, Φ a = 1 → a ∈ Subgroup.center ↥C₀ := by
  let Ψ : ↥C₀ →* W' := π.comp (Subgroup.inclusion hC₀W)
  have hΨC : ∀ a : ↥C₀, Ψ a ∈ C := by
    intro a
    rw [← hC]
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hC₀W a,
        Subgroup.mem_subgroupOf.mpr (by simpa [Subgroup.coe_inclusion] using a.2), rfl⟩
  refine ⟨MonoidHom.codRestrict Ψ C hΨC, ?_, ?_⟩
  · intro c
    have hc : (c : W') ∈ (C₀.subgroupOf W).map π := by rw [hC]; exact c.2
    obtain ⟨w, hw, hwπ⟩ := Subgroup.mem_map.mp hc
    refine ⟨⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩, ?_⟩
    apply Subtype.ext
    simp only [MonoidHom.codRestrict_apply, Ψ, MonoidHom.comp_apply]
    rw [show Subgroup.inclusion hC₀W ⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩ = w from
      Subtype.ext rfl]
    exact hwπ
  · intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hmem : ((Subgroup.inclusion hC₀W a : ↥W) : X) ∈
        Subgroup.centralizer (C₀ : Set X) := by
      apply hker
      have hΨ1 : Ψ a = 1 := by
        have := congrArg (fun x : ↥C => (x : W')) ha
        simpa [MonoidHom.codRestrict_apply] using this
      exact hΨ1
    have hcw := Subgroup.mem_centralizer_iff.mp hmem (g : X) g.2
    simpa [Subgroup.coe_inclusion] using hcw

theorem ggExists_surjective_map_subtype {N : Subgroup X} (S' : Subgroup ↥N) :
    ∃ Φ : ↥(S'.map N.subtype) →* ↥S', Function.Surjective Φ := by
  let e := S'.equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨e.symm.toMonoidHom, e.symm.surjective⟩

end Chains

section Facts

theorem ggIsSimpleGroup_of_marking {G : Type*} [Group G] {G₀ : Subgroup G}
    {P : LargeEvenMarkProp ↥G₀} (h : LargeEvenMarking ↥G₀ P)
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) : IsSimpleGroup ↥G₀ := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, -⟩ := largeEvenRawDatum_exists hraw
  have hcenter : Subgroup.center ↥G₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzc : (z : G) ∈ Subgroup.centralizer (G₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : (⟨g, hg⟩ : ↥G₀) * z = z * ⟨g, hg⟩ :=
        Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
      exact congrArg Subtype.val hg'
    rw [hC] at hzc
    exact Subtype.ext (by simpa using Subgroup.mem_bot.mp hzc)
  haveI : IsSimpleGroup R := hs
  let e : ↥G₀ ≃* R :=
    ((QuotientGroup.quotientBot.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).trans θ
  exact e.isSimpleGroup

theorem ggIsElemAbelian_closure_pair {G : Type*} [Group G] {p : ℕ} {b e : G} (hb : b ^ p = 1)
    (he : e ^ p = 1) (hbe : Commute b e) :
    IsElemAbelian p (Subgroup.closure ({b, e} : Set G)) := by
  have hpair : ({b, e} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    all_goals first | exact hbe | exact hbe.symm | exact Commute.refl b | exact Commute.refl e
  haveI hcomm : IsMulCommutative ↥(Subgroup.closure ({b, e} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  refine ⟨hcomm, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha
      · rw [ha]; exact hb
      · rw [ha]; exact he
  | one => simp
  | mul a c ha hc iha ihc =>
      have hac : a * c = c * a :=
        congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(Subgroup.closure ({b, e} : Set G)))
          (⟨c, hc⟩ : ↥(Subgroup.closure ({b, e} : Set G))))
      rw [Commute.mul_pow hac, iha, ihc, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem ggCentralizer_closure_pair_set {G : Type*} [Group G] (b e : G) :
    Subgroup.centralizer ((Subgroup.closure ({b, e} : Set G) : Subgroup G) : Set G) =
      Subgroup.centralizer ({b, e} : Set G) :=
  Subgroup.centralizer_closure _

theorem ggCommutator_eq_top_of_perfect {G : Type*} [Group G] {S : Subgroup G} (h : ⁅S, S⁆ = S) :
    commutator ↥S = ⊤ :=
  Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr h)

end Facts

end CFSG.StandardType
