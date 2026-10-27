module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTen
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsNine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

@[expose] def centralizerHat (V V₁ : Subgroup G) : Subgroup G :=
  centralizerMod (centerOf (uA V V₁)) (Subgroup.normalizer (V₁ : Set G)) (uA V V₁)

namespace Setting

theorem uA_le_centralizerHat (S : Setting V V₁ L T) : uA V V₁ ≤ centralizerHat V V₁ := by
  intro u hu
  refine ⟨S.uA_le_normalizer hu, ?_, fun u' hu' => ?_⟩
  · exact normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hu)
  · exact S.V₁_le_centerOf (S.commutator_mem hu hu')

omit [Finite G] in
theorem normalizer_le_normalizer_centralizerHat :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (centralizerHat V V₁ : Set G) :=
  CFSG.Quasithin.le_normalizer_centralizerMod
    (fun _ hx => normalizer_le_normalizer_centerOf _ (normalizer_le_normalizer_uA V V₁ hx))
    Subgroup.le_normalizer
    (fun _ hx => normalizer_le_normalizer_uA V V₁ hx)

theorem exists_mul_mem_centralizer_of_mem_inf (S : Setting V V₁ L T) {y : G}
    (hyH : y ∈ Subgroup.normalizer (V₁ : Set G)) (hyN : y ∈ Subgroup.normalizer (V : Set G)) :
    ∃ u ∈ uA V V₁, u⁻¹ * y ∈ Subgroup.centralizer (V : Set G) := by
  by_cases hyC : y ∈ Subgroup.centralizer (V : Set G)
  · exact ⟨1, Subgroup.one_mem _, by simpa using hyC⟩
  · obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uA V V₁, u₀ ∉ wA V V₁ := by
      by_contra hall
      push Not at hall
      exact S.not_le_centralizer_V fun u hu => (hall u hu).2
    have hu₀C : u₀ ∉ Subgroup.centralizer (V : Set G) := fun hc => hu₀W ⟨hu₀U, hc⟩
    have hyZ : y ∈ Subgroup.centralizer (V₁ : Set G) := by
      rw [← S.normalizer_eq_centralizer]
      exact hyH
    exact ⟨u₀, hu₀U, S.inv_mul_mem_centralizer_V (S.uA_le_normalizer_V hu₀U) hyN
      (S.uA_le_centralizer hu₀U) hyZ hu₀C hyC⟩

theorem inf_normalizer_le_normalizer_sup_centralizerHat (S : Setting V V₁ L T) {K : Subgroup G}
    (hK : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((K ⊔ centralizerHat V V₁ : Subgroup G) : Set G) := by
  rintro y ⟨hyH, hyN⟩
  obtain ⟨u, hu, huc⟩ := S.exists_mul_mem_centralizer_of_mem_inf hyH hyN
  have hyeq : y = u * (u⁻¹ * y) := by group
  rw [hyeq]
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer
    (le_sup_right (a := K) (b := centralizerHat V V₁) (S.uA_le_centralizerHat hu))) ?_
  have hcH : u⁻¹ * y ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (S.V₁_le) huc)
  exact Subgroup.inf_normalizer_le_normalizer_sup K (centralizerHat V V₁)
    ⟨hK huc, normalizer_le_normalizer_centralizerHat hcH⟩

theorem relIndex_wA_eq_two (S : Setting V V₁ L T) :
    (wA V V₁).relIndex (uA V V₁) = 2 := by
  obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uA V V₁, u₀ ∉ wA V V₁ := by
    by_contra hall
    push Not at hall
    exact S.not_le_centralizer_V fun u hu => (hall u hu).2
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨u₀, hu₀U⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ wA V V₁
  · right
    refine ⟨hb, fun hbu => hu₀W ?_⟩
    have := (wA V V₁).mul_mem ((wA V V₁).inv_mem hb) hbu
    simpa using this
  · left
    refine ⟨?_, hb⟩
    have hb' : (b : G)⁻¹ ∉ wA V V₁ := fun hb'' => hb (by simpa using (wA V V₁).inv_mem hb'')
    rcases S.mem_wA_or_inv_mul_mem ((uA V V₁).inv_mem b.2) hu₀U hb' with h1 | h1
    · exact absurd h1 hu₀W
    · simpa using h1

section

variable (S : Setting V V₁ L T) {g : G} (hg : Good V₁ L g)

include S hg

theorem thirteen_one : V ≤ wA V V₁ ⊓ rconj (wA V V₁) g := by
  rw [S.wA_inf_rconj_eq hg]
  exact S.le_inf_rconj hg

theorem thirteen_two : rconj (centerOf (uA V V₁)) g ≤ Subgroup.centralizer (V : Set G) := by
  intro z hz
  have hzC : z ∈ centerOf (rconj (uA V V₁) g) := by
    rw [centerOf_rconj]
    exact hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp hzC.2 v ((S.le_inf_rconj hg) hv).2

omit [Finite G] in
theorem centralizer_V_le_normalizer_rconj_uA :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (rconj (uA V V₁) g : Set G) := by
  intro c hc
  refine mem_normalizer_rconj_of_conj_mem ?_
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans S.LT_le_normalizer_V) hg.mem
  have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hgN) c).mp hc
  exact normalizer_le_normalizer_uA V V₁
    (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (S.V₁_le) hc'))

omit [Finite G] in
theorem centralizer_V_le_normalizer_rconj_wA :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (rconj (wA V V₁) g : Set G) := by
  intro c hc
  refine mem_normalizer_rconj_of_conj_mem ?_
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans S.LT_le_normalizer_V) hg.mem
  have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hgN) c).mp hc
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨normalizer_le_normalizer_uA V V₁
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (S.V₁_le) hc')),
      Subgroup.le_normalizer hc'⟩

omit [Finite G] in
theorem centralizer_V_le_normalizer_rconj_centerOf :
    Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer (rconj (centerOf (uA V V₁)) g : Set G) := by
  intro c hc
  rw [← centerOf_rconj]
  exact normalizer_le_normalizer_centerOf _
    (S.centralizer_V_le_normalizer_rconj_uA hg hc)

theorem twelve_two :
    Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer ((rconj (wA V V₁) g ⊔ centralizerHat V V₁ : Subgroup G) : Set G) ∧
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer
          ((rconj (centerOf (uA V V₁)) g ⊔ centralizerHat V V₁ : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer
        ((rconj (wA V V₁) g ⊔ centralizerHat V V₁ : Subgroup G) : Set G) := by
  have h1 := S.inf_normalizer_le_normalizer_sup_centralizerHat
    (S.centralizer_V_le_normalizer_rconj_wA hg)
  refine ⟨h1, S.inf_normalizer_le_normalizer_sup_centralizerHat
    (S.centralizer_V_le_normalizer_rconj_centerOf hg), fun t ht => h1 ⟨?_, ?_⟩⟩
  · exact S.base.T_le_normV₁ ht
  · exact S.base.T_le_normV ht

theorem eleven_one :
    ⁅wA V V₁, rconj (wA V V₁) g⁆ ≤ wA V V₁ ⊓ rconj (wA V V₁) g :=
  S.commutator_wA_rconj_le hg

theorem eleven_two :
    IsElemAbelian 2 (wA V V₁ ⊓ rconj (wA V V₁) g) ∧
      frattiniOf (wA V V₁ ⊓ rconj (wA V V₁) g) = ⊥ := by
  have hE : IsElemAbelian 2 (wA V V₁ ⊓ rconj (wA V V₁) g) := by
    rw [S.wA_inf_rconj_eq hg]
    exact S.isElemAbelian_inf_rconj hg
  refine ⟨hE, ?_⟩
  rw [eq_bot_iff]
  refine frattiniOf_le_of_forall (fun x hx y hy => ?_) (fun x hx => ?_)
  · have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [Subgroup.mem_bot]
    calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = 1 := by group
  · rw [Subgroup.mem_bot]
    exact hE.2 x hx

theorem eleven_four :
    centralizerMod (centerOf (uA V V₁)) (wA V V₁ ⊓ rconj (wA V V₁) g) (rconj (wA V V₁) g) ⊔
      centerOf (uA V V₁) = V ⊔ centerOf (uA V V₁) := by
  have hE : wA V V₁ ⊓ rconj (wA V V₁) g = uA V V₁ ⊓ rconj (uA V V₁) g :=
    S.wA_inf_rconj_eq hg
  have hVE : V ≤ wA V V₁ ⊓ rconj (wA V V₁) g := by
    rw [hE]
    exact S.le_inf_rconj hg
  have hV1gV : rconj V₁ g ≤ V := S.l2Setting.V₁_le_rconj_V hg.mem
  have hCX : ∀ v ∈ V, v ∈ centerOf (rconj (wA V V₁) g) := by
    intro v hv
    rw [S.centerOf_rconj_wA_eq hg]
    exact Subgroup.mem_sup_left hv
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro e ⟨heE, -, hecomm⟩
    have heX : e ∈ rconj (wA V V₁) g := heE.2
    have heUg : e ∈ rconj (uA V V₁) g := by
      rw [hE] at heE
      exact heE.2
    have hcX : ∀ x ∈ rconj (wA V V₁) g, x * e = e * x := by
      intro x hx
      have hxUg : x ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g hx
      have h1 : e * x * e⁻¹ * x⁻¹ ∈ rconj V₁ g := by
        rw [mem_rconj]
        have he' : g * e * g⁻¹ ∈ uA V V₁ := mem_rconj.mp heUg
        have hx' : g * x * g⁻¹ ∈ uA V V₁ := mem_rconj.mp hxUg
        have := S.commutator_mem he' hx'
        have e1 : g * (e * x * e⁻¹ * x⁻¹) * g⁻¹ =
            (g * e * g⁻¹) * (g * x * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ := by group
        rw [e1]
        exact this
      have h2 : e * x * e⁻¹ * x⁻¹ ∈ centerOf (uA V V₁) := hecomm x hx
      have h3 : e * x * e⁻¹ * x⁻¹ ∈ rconj V₁ g ⊓ centerOf (uA V V₁) := ⟨h1, h2⟩
      rw [S.nine_seven hg] at h3
      have h4 : e * x * e⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h3
      have h5 : e * x = x * e := by
        calc e * x = (e * x * e⁻¹ * x⁻¹) * x * e := by group
          _ = x * e := by rw [h4]; group
      exact h5.symm
    have heC : e ∈ centerOf (rconj (wA V V₁) g) :=
      ⟨heX, Subgroup.mem_centralizer_iff.mpr hcX⟩
    rw [S.centerOf_rconj_wA_eq hg] at heC
    have hVc : ∀ v ∈ V, ∀ z ∈ rconj (centerOf (uA V V₁)) g, v * z = z * v := by
      intro v hv z hz
      exact (Subgroup.mem_centralizer_iff.mp (hCX v hv).2 z
        (rconj_centerOf_le_rconj_wA V V₁ g hz)).symm
    obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hVc heC
    have hzU : z ∈ uA V V₁ := by
      have h1 : v⁻¹ * (v * z) ∈ uA V V₁ :=
        (uA V V₁).mul_mem ((uA V V₁).inv_mem (le_uA V V₁ hv))
          (by rw [hE] at heE; exact heE.1)
      simpa using h1
    have hz' : z ∈ rconj (centerOf (uA V V₁)) g ⊓ uA V V₁ := ⟨hz, hzU⟩
    rw [S.ten_one_symm hg] at hz'
    have hz'' : z ∈ V ⊔ centerOf (uA V V₁) :=
      (sup_le (inf_le_left.trans le_sup_right) (hV1gV.trans le_sup_left)) hz'
    exact (V ⊔ centerOf (uA V V₁)).mul_mem (Subgroup.mem_sup_left hv) hz''
  · refine sup_le (fun v hv => Subgroup.mem_sup_left ?_) le_sup_right
    refine ⟨hVE hv, normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer
      (le_uA V V₁ hv)), fun x hx => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp (hCX v hv).2 x hx
    have e3 : v * x * v⁻¹ * x⁻¹ = 1 := by
      calc v * x * v⁻¹ * x⁻¹ = (x * v) * v⁻¹ * x⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e3]
    exact Subgroup.one_mem _

theorem eleven_five :
    2 * (wA V V₁ ⊓ rconj (wA V V₁) g ⊓ centerOf (uA V V₁)).relIndex
        (wA V V₁ ⊓ rconj (wA V V₁) g) *
      (rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)).relIndex
        (rconj (wA V V₁) g) = (centerOf (uA V V₁)).relIndex (uA V V₁) := by
  have hZuU : centerOf (uA V V₁) ≤ uA V V₁ := inf_le_left
  have hEW : wA V V₁ ⊓ rconj (wA V V₁) g ≤ wA V V₁ := inf_le_left
  have hEU : wA V V₁ ⊓ rconj (wA V V₁) g ≤ uA V V₁ := hEW.trans (wA_le_uA V V₁)
  have hZuW : centerOf (uA V V₁) ≤ wA V V₁ := centerOf_uA_le_wA V V₁
  have hsupW : centerOf (uA V V₁) ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g) ≤ wA V V₁ :=
    sup_le hZuW hEW
  have hchain : (centerOf (uA V V₁)).relIndex (uA V V₁) =
      (centerOf (uA V V₁)).relIndex (centerOf (uA V V₁) ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)) *
        (centerOf (uA V V₁) ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)).relIndex (wA V V₁) *
          (wA V V₁).relIndex (uA V V₁) := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hsupW,
      Subgroup.relIndex_mul_relIndex _ _ _ hZuW (wA_le_uA V V₁)]
  have hNorm : uA V V₁ ≤ Subgroup.normalizer (centerOf (uA V V₁) : Set G) :=
    fun u hu => normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hu)
  have hsecond : (centerOf (uA V V₁)).relIndex
      (centerOf (uA V V₁) ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)) =
      (wA V V₁ ⊓ rconj (wA V V₁) g ⊓ centerOf (uA V V₁)).relIndex
        (wA V V₁ ⊓ rconj (wA V V₁) g) := by
    have : ((centerOf (uA V V₁)).subgroupOf (uA V V₁)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNorm
    have h1 := Subgroup.relIndex_sup_left (K := (centerOf (uA V V₁)).subgroupOf (uA V V₁))
      (H := (wA V V₁ ⊓ rconj (wA V V₁) g).subgroupOf (uA V V₁))
    rw [← Subgroup.subgroupOf_sup hZuU hEU, Subgroup.relIndex_subgroupOf (sup_le hZuU hEU),
      Subgroup.relIndex_subgroupOf hEU] at h1
    rw [h1, ← Subgroup.inf_relIndex_right, inf_comm]
  have hgE : g ∈ Subgroup.normalizer ((wA V V₁ ⊓ rconj (wA V V₁) g : Subgroup G) : Set G) :=
    S.sup_le_normalizer_inf_rconj_wA hg (hg.mem_sup _)
  have hconj : ∀ A B : Subgroup G, (rconj A g).relIndex (rconj B g) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective A B (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulEquiv.injective _)
  have hthird : (rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)).relIndex
      (rconj (wA V V₁) g) =
      (centerOf (uA V V₁) ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)).relIndex (wA V V₁) := by
    have h1 := hconj (centerOf (uA V V₁) ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)) (wA V V₁)
    rw [rconj_sup_eq, rconj_eq_of_mem_normalizer hgE] at h1
    exact h1
  rw [hthird, hchain, hsecond, S.relIndex_wA_eq_two]
  ring

end

end Setting

end L128A

end CFSG.Quasithin.H13
