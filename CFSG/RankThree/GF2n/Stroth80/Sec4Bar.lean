module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Swap
public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Basic

variable [(Q.subgroupOf M).Normal]

theorem Ctx.swapHyp (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) : SwapHyp (Mbar M Q) (bar M Q (LB M Q B)) where
  comm a ha b hb :=
    congrArg Subtype.val (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  sq a ha := hc.isElemAbelian_bar_LB.2 a ha
  sylow S hS hΛS := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LargeExtraspecial.le_normalizer_of_isWeaklyClosed
      (fun g hg => hc.weaklyClosed_bar_LB hw hn hno g hg) hS hΛS


theorem Ctx.Lgen_le_H0_sec4x (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ H0 M Z := by
  refine iSup₂_le fun m hm => ?_
  intro x hx
  have hl : m⁻¹ * x * m ∈ LB M Q B := mem_conjSubgroup.mp hx
  have hxM : x ∈ M := conj_le_M hc.LB_le_M hm hx
  refine ⟨hxM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hz' : m⁻¹ * z * m ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hc.hyp.Z_normal.2 hm)) z).mp hz
    simpa using this
  have h1 := hc.LB_centralizes_Z hl _ hz'
  have h2 : x * z * x⁻¹ = z := by
    calc x * z * x⁻¹ = m * ((m⁻¹ * x * m) * (m⁻¹ * z * m) * (m⁻¹ * x * m)⁻¹) * m⁻¹ := by group
      _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [h1]
      _ = z := by group
  calc z * x = (x * z * x⁻¹) * x := by rw [h2]
    _ = x * z := by group

theorem Ctx.bar_Lgen_le_bar_H0 (hc : Ctx M Q Z B) :
    bar M Q (Lgen M (LB M Q B)) ≤ bar M Q (H0 M Z) :=
  Subgroup.map_mono fun x hx => hc.Lgen_le_H0_sec4x hx

theorem Ctx.noComm (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    ∀ X : Subgroup (Mbar M Q), CFSG.IsQuasisimple ↥X →
      ¬ ∀ x ∈ X, ∀ m ∈ bar M Q (Lgen M (LB M Q B)), x * m = m * x := by
  intro X hXq hcomm
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  refine hc.false_of_comm h35 X hXq fun x hx t ht => hcomm x hx _ (hc.bar_LB_le_bar_Lgen ?_)
  exact ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩

theorem Ctx.compSimple (h34 : Stroth34Statement) (h44 : Stroth44Statement) (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) :
    CompSimple (Mbar M Q) :=
  compSimple_of_odd hc.pCore_two_Mbar hc.normal_bar_Lgen hc.bar_LB_le_bar_Lgen
    (hc.noComm h34 hw hn hno hgen)
    (fun A hAM hΛA hodd => h44 G M Q Z B hc n hw hn hno hgen A (hAM.trans hc.bar_Lgen_le_bar_H0)
      hΛA hodd)

theorem bar_le_normalizer_of_le_normalizer {L S : Subgroup G} (hQL : Q ≤ L) (hLM : L ≤ M)
    (hSM : S ≤ M) (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    bar M Q S ≤ Subgroup.normalizer (bar M Q L : Set (Mbar M Q)) := by
  rintro _ ⟨y, hy, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨w, hw, rfl⟩ := hz
  have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.mp hy
  have hyN := (Subgroup.mem_normalizer_iff.mp (hSN hyS) (w : G)).mp (Subgroup.mem_subgroupOf.mp hw)
  refine ⟨y * w * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
  show (y : G) * (w : G) * (y : G)⁻¹ ∈ L
  exact hyN

theorem Ctx.bar_CN_le_normalizer (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {t : G}
    (ht : t ∈ LB M Q B) :
    bar M Q (hc.CN t) ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  refine bar_le_normalizer_of_le_normalizer (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M
    (fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1) fun x hx => ?_
  have h1 := hc.CN_normalizes_conj_LB h35 ht (h := 1) (Subgroup.one_mem _) hx
  rwa [conjSubgroup_one_sec4] at h1


theorem Ctx.bar_Rt_comm (hc : Ctx M Q Z B) {t : M} :
    ∀ x ∈ bar M Q (Rt M (LB M Q B) (t : G)),
      x * (QuotientGroup.mk t : Mbar M Q) = QuotientGroup.mk t * x := by
  rintro _ ⟨r, hr, rfl⟩
  have hrR : (r : G) ∈ Rt M (LB M Q B) (t : G) := Subgroup.mem_subgroupOf.mp hr
  have h1 : ⁅(r : G), (t : G)⁆ ∈ Q := hc.Rt_comm_mem_Q hrR
  have h2 : (⁅r, t⁆ : ↥M) ∈ Q.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)
  have h3 : ⁅(QuotientGroup.mk' (Q.subgroupOf M) r : Mbar M Q),
      QuotientGroup.mk' (Q.subgroupOf M) t⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem Ctx.bar_CN_conj_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r n : Mbar M Q}
    (hr : r ∈ bar M Q (Rt M (LB M Q B) t)) (hn : n ∈ bar M Q (hc.CN t)) :
    r * n * r⁻¹ ∈ bar M Q (hc.CN t) := by
  obtain ⟨r', hr', rfl⟩ := hr
  obtain ⟨n', hn', rfl⟩ := hn
  refine ⟨r' * n' * r'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
  exact hc.CN_conj_mem ht (Subgroup.mem_subgroupOf.mp hr') (Subgroup.mem_subgroupOf.mp hn')

theorem Ctx.bar_LB_le_bar_Rt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    bar M Q (LB M Q B) ≤ bar M Q (Rt M (LB M Q B) t) :=
  Subgroup.map_mono fun x hx => le_Rt (M := M) (LB M Q B) ht hx

theorem Ctx.component_le_bar_Rt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {C : Subgroup (Mbar M Q)} (hC : IsComponent C) {t : M}
    (ht : (t : G) ∈ LB M Q B)
    (hcent : ∀ x ∈ C, x * (QuotientGroup.mk t : Mbar M Q) = QuotientGroup.mk t * x) :
    C ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
  have hΛ := hc.swapHyp hw hn hno
  have htΛ : (QuotientGroup.mk t : Mbar M Q) ∈ bar M Q (LB M Q B) :=
    ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  by_cases hN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (C : Set (Mbar M Q))
  · have hne : bar M Q (LB M Q B) ⊓ C ≠ ⊥ :=
      hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hC.1 hN
    refine hc.le_bar_Rt_of_normalClosure ht (S := bar M Q (LB M Q B) ⊓ C) inf_le_left inf_le_right
      (normalClosure_subgroupOf_eq_top_of_forall inf_le_right fun N hNn hSN => ?_) hcent
    refine hcs.le_of_inf_ne_bot hC hNn fun h0 => hne ?_
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ N ⊓ C := ⟨hSN hx, hx.2⟩
    rw [h0] at this
    exact this
  ·
    obtain ⟨s, hsΛ, hsC⟩ := Set.not_subset.mp hN
    have hne : conjSubgroup s C ≠ C := fun h => hsC (conjSubgroup_eq_self_iff.mp h)
    obtain ⟨d, hdY, hd1, -, hdΛ⟩ := swap_exists_involution hΛ hcs hC hsΛ hne
    set K : Subgroup (Mbar M Q) := C ⊔ conjSubgroup s C with hK
    have hC' := isComponent_conjSubgroup s hC
    have hCC' := swap_comm hC hne
    have hKcent : ∀ x ∈ K, x * (QuotientGroup.mk t : Mbar M Q) = QuotientGroup.mk t * x := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hCC' hx
      obtain ⟨b₀, hb₀, rfl⟩ : ∃ b₀ ∈ C, b = s * b₀ * s⁻¹ :=
        ⟨s⁻¹ * b * s, (mem_conjSubgroup (g := s) (T := C) (x := b)).mp hb, by group⟩
      have h1 := hcent a ha
      have h2 := hcent b₀ hb₀
      have h3 : s * (QuotientGroup.mk t : Mbar M Q) = QuotientGroup.mk t * s :=
        hΛ.comm s hsΛ _ htΛ
      calc a * (s * b₀ * s⁻¹) * QuotientGroup.mk t
          = a * (s * (b₀ * (s⁻¹ * QuotientGroup.mk t))) := by group
        _ = a * (s * (b₀ * (QuotientGroup.mk t * s⁻¹))) := by
          congr 3
          calc (s⁻¹ * (QuotientGroup.mk t : Mbar M Q))
              = s⁻¹ * (QuotientGroup.mk t * s) * s⁻¹ := by group
            _ = s⁻¹ * (s * QuotientGroup.mk t) * s⁻¹ := by rw [h3]
            _ = QuotientGroup.mk t * s⁻¹ := by group
        _ = a * (s * ((b₀ * QuotientGroup.mk t) * s⁻¹)) := by group
        _ = a * (s * ((QuotientGroup.mk t * b₀) * s⁻¹)) := by rw [h2]
        _ = a * ((s * QuotientGroup.mk t) * (b₀ * s⁻¹)) := by group
        _ = a * ((QuotientGroup.mk t * s) * (b₀ * s⁻¹)) := by rw [h3]
        _ = (a * QuotientGroup.mk t) * (s * b₀ * s⁻¹) := by group
        _ = (QuotientGroup.mk t * a) * (s * b₀ * s⁻¹) := by rw [h1]
        _ = QuotientGroup.mk t * (a * (s * b₀ * s⁻¹)) := by group
    have hKR : K ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
      refine hc.le_bar_Rt_of_normalClosure ht (S := Subgroup.zpowers (d * (s * d * s⁻¹)))
        ?_ ?_ (normalClosure_subgroupOf_eq_top_of_forall ?_ fun N hNn hSN => ?_) hKcent
      · rw [Subgroup.zpowers_le]; exact hdΛ
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mul_mem_sup hdY (mul_mem_conjSubgroup_iff.mpr hdY)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mul_mem_sup hdY (mul_mem_conjSubgroup_iff.mpr hdY)
      · refine swap_sup_le hcs hC hne (fun c hc' n hn' => hNn c ((le_sup_left : C ≤ K) hc') n hn')
          (fun c hc' n hn' => hNn c ((le_sup_right : conjSubgroup s C ≤ K) hc') n hn') hdY hd1 ?_
        exact hSN (Subgroup.mem_zpowers _)
    exact le_sup_left.trans hKR


theorem Ctx.exists_bar_hom (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ι : Type}
    [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {Gc : Subgroup (GL ι K)}
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφr : φ.range = Gc)
    (hφk : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) :
    ∃ π : ↥(bar M Q (Rt M (LB M Q B) t)) →* ↥Gc, Function.Surjective π ∧
      ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)),
        π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t) := by
  classical
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx, fun v hv =>
      hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  let ψ : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hψ : ∀ r : ↥(Rt M (LB M Q B) t),
      ψ r = QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hRM r.2⟩ := fun r => rfl
  have hmem : ∀ r : ↥(Rt M (LB M Q B) t), ψ r ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  let f : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) := ψ.codRestrict _ hmem
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp y.2
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    refine ⟨⟨(r : G), hrR⟩, Subtype.ext ?_⟩
    show ψ ⟨(r : G), hrR⟩ = (y : Mbar M Q)
    rw [hψ]
    have : (⟨((⟨(r : G), hrR⟩ : ↥(Rt M (LB M Q B) t)) : G),
        hRM (⟨(r : G), hrR⟩ : ↥(Rt M (LB M Q B) t)).2⟩ : ↥M) = r := Subtype.ext rfl
    rw [this, hry]
  have hker : f.ker ≤ φ.ker := by
    intro r hr
    have h1 : ψ r = 1 := congrArg Subtype.val hr
    rw [hψ] at h1
    have h2 : (⟨(r : G), hRM r.2⟩ : ↥M) ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
    rw [hφk]
    exact Subgroup.mem_subgroupOf.mpr (hQN (Subgroup.mem_subgroupOf.mp h2))
  let π₀ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL ι K :=
    (MonoidHom.liftOfSurjective f hfsurj) ⟨φ, hker⟩
  have hπ₀ : ∀ r : ↥(Rt M (LB M Q B) t), π₀ (f r) = φ r := fun r =>
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hfsurj)
      (Function.rightInverse_surjInv hfsurj) ⟨φ, hker⟩ r
  have hπmem : ∀ x, π₀ x ∈ Gc := by
    intro x
    obtain ⟨r, rfl⟩ := hfsurj x
    rw [hπ₀, ← hφr]
    exact ⟨r, rfl⟩
  refine ⟨π₀.codRestrict Gc hπmem, ?_, ?_⟩
  · intro g
    have hg : (g : GL ι K) ∈ φ.range := hφr ▸ g.2
    obtain ⟨r, hr⟩ := hg
    exact ⟨f r, Subtype.ext (show π₀ (f r) = (g : GL ι K) by rw [hπ₀, hr])⟩
  · intro x
    obtain ⟨r, rfl⟩ := hfsurj x
    have hπx : (π₀.codRestrict Gc hπmem (f r) = 1) ↔ φ r = 1 := by
      rw [← hπ₀]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hπx]
    constructor
    · intro h
      have h1 : r ∈ φ.ker := h
      rw [hφk] at h1
      have h2 : (r : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp h1
      exact ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr h2, rfl⟩
    · intro h
      obtain ⟨y, hy, hyr⟩ := h
      have hyCN : (y : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hy
      have h1 : ψ r = QuotientGroup.mk' (Q.subgroupOf M) y := by
        have : ψ r = (f r : Mbar M Q) := rfl
        rw [this, ← hyr]
      rw [hψ] at h1
      have h2 := QuotientGroup.eq.mp h1
      have h3 : ((r : G))⁻¹ * (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp h2
      have h4 : (r : G) ∈ hc.CN t := by
        have e : (r : G) = (y : G) * ((r : G)⁻¹ * (y : G))⁻¹ := by group
        rw [e]
        exact (hc.CN t).mul_mem hyCN ((hc.CN t).inv_mem (hQN h3))
      have h5 : r ∈ φ.ker := by
        rw [hφk]
        exact Subgroup.mem_subgroupOf.mpr h4
      exact h5


theorem Ctx.classical_quotient (h310 : Stroth310Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) (hR : Rt M (LB M Q B) t ≠ LB M Q B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Gc : Type) (_ : Group Gc)
      (π : ↥(bar M Q (Rt M (LB M Q B) t)) →* Gc),
      Nat.card K = Nat.card Z ∧ Function.Surjective π ∧
        (∀ x : ↥(bar M Q (Rt M (LB M Q B) t)),
          π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧ IsClassicalOver K Gc := by
  rcases h310 G M Q Z B hc n hw hn hno hgen t ht htQ with hRL | ⟨K, hF, hFin, hK, hnat⟩
  · exact absurd hRL hR
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : Subgroup (GL ι K)} {V : Subgroup G},
      NaturalRep K X (Rt M (LB M Q B) t) V Z (hc.CN t) → IsClassicalOver K ↥X →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Gc : Type) (_ : Group Gc)
        (π : ↥(bar M Q (Rt M (LB M Q B) t)) →* Gc),
        Nat.card K = Nat.card Z ∧ Function.Surjective π ∧
          (∀ x : ↥(bar M Q (Rt M (LB M Q B) t)),
            π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧ IsClassicalOver K Gc := by
    intro ι _ _ X V hnat' hX
    obtain ⟨φ, hφr, hφk, -⟩ := hnat'
    obtain ⟨π, hπs, hπk⟩ := hc.exists_bar_hom ht φ hφr hφk
    exact ⟨K, hF, hFin, inferInstance, ↥X, inferInstance, π, hK, hπs, hπk, hX⟩
  rcases hnat with ⟨m, hm, hn'⟩ | ⟨m, hm, hn'⟩ | ⟨m, hm, hn'⟩ | ⟨m, b, c, hm, hirr, hn'⟩
  · exact key hn' (Or.inl ⟨m, hm, ⟨MulEquiv.refl _⟩⟩)
  · exact key hn' (Or.inr (Or.inl ⟨m, hm, ⟨MulEquiv.refl _⟩⟩))
  · exact key hn' (Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨MulEquiv.refl _⟩⟩)))
  · exact key hn' (Or.inr (Or.inr (Or.inr ⟨m, b, c, hm, hirr, ⟨MulEquiv.refl _⟩⟩)))

theorem Ctx.inf_CN_eq_bot_of_not_le (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {X : Subgroup (Mbar M Q)} [IsSimpleGroup ↥X] (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hX : ¬ X ≤ bar M Q (hc.CN t)) : X ⊓ bar M Q (hc.CN t) = ⊥ := by
  have hnorm : ((X ⊓ bar M Q (hc.CN t)).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨X.mul_mem (X.mul_mem g.2 hn.1) (X.inv_mem g.2),
      hc.bar_CN_conj_mem ht (hXR g.2) hn.2⟩
  rcases hnorm.eq_bot_or_eq_top with hb | htop
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥X) ∈ (X ⊓ bar M Q (hc.CN t)).subgroupOf X := hx
    rw [hb, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    apply hX
    intro x hx
    exact (Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥X) ∈
      (X ⊓ bar M Q (hc.CN t)).subgroupOf X by rw [htop]; exact Subgroup.mem_top _)).2

theorem Ctx.not_le_CN_of_simple (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {t : G}
    (ht : t ∈ LB M Q B) {X : Subgroup (Mbar M Q)} [IsSimpleGroup ↥X]
    (hXnab : ∃ a b : ↥X, a * b ≠ b * a) (hΛX : bar M Q (LB M Q B) ⊓ X ≠ ⊥) :
    ¬ X ≤ bar M Q (hc.CN t) := by
  intro hXN
  have hXΛ : X ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := fun x hx =>
    hc.bar_CN_le_normalizer h34 hw hn hno hgen ht (hXN hx)
  have hnorm2 : ((bar M Q (LB M Q B) ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, X.mul_mem (X.mul_mem g.2 hn.2) (X.inv_mem g.2)⟩
    have := (Subgroup.mem_normalizer_iff.mp (hXΛ g.2) (n : Mbar M Q)).mp hn.1
    exact this
  rcases hnorm2.eq_bot_or_eq_top with hb2 | ht2
  · apply hΛX
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥X) ∈ (bar M Q (LB M Q B) ⊓ X).subgroupOf X := hx
    rw [hb2, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · obtain ⟨a, b, hab⟩ := hXnab
    have ha : (a : Mbar M Q) ∈ bar M Q (LB M Q B) := by
      have : (a : ↥X) ∈ (bar M Q (LB M Q B) ⊓ X).subgroupOf X := by
        rw [ht2]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    have hb' : (b : Mbar M Q) ∈ bar M Q (LB M Q B) := by
      have : (b : ↥X) ∈ (bar M Q (LB M Q B) ⊓ X).subgroupOf X := by
        rw [ht2]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    have hcomm := (hc.swapHyp hw hn hno).comm _ ha _ hb'
    exact hab (Subtype.ext hcomm)

theorem Ctx.inf_CN_eq_bot_of_simple (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {t : G}
    (ht : t ∈ LB M Q B) {X : Subgroup (Mbar M Q)} [IsSimpleGroup ↥X]
    (hXR : X ≤ bar M Q (Rt M (LB M Q B) t)) (hXnab : ∃ a b : ↥X, a * b ≠ b * a)
    (hΛX : bar M Q (LB M Q B) ⊓ X ≠ ⊥) : X ⊓ bar M Q (hc.CN t) = ⊥ :=
  hc.inf_CN_eq_bot_of_not_le ht hXR (hc.not_le_CN_of_simple h34 hw hn hno hgen ht hXnab hΛX)

theorem Ctx.component_inf_CN_eq_bot (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {t : G} (ht : t ∈ LB M Q B) {C : Subgroup (Mbar M Q)}
    (hC : IsComponent C) (hCR : C ≤ bar M Q (Rt M (LB M Q B) t)) :
    C ⊓ bar M Q (hc.CN t) = ⊥ := by
  haveI := isSimpleGroup_of_center_eq_bot hC (hcs C hC)
  by_cases hN : bar M Q (LB M Q B) ≤ Subgroup.normalizer (C : Set (Mbar M Q))
  · exact hc.inf_CN_eq_bot_of_simple h34 hw hn hno hgen ht hCR (exists_noncomm_of_isComponent hC)
      (hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hC.1 hN)
  · refine hc.inf_CN_eq_bot_of_not_le ht hCR fun hCN => ?_
    obtain ⟨s, hsΛ, hsC⟩ := Set.not_subset.mp hN
    have hne : conjSubgroup s C ≠ C := fun h => hsC (conjSubgroup_eq_self_iff.mp h)
    exact swap_not_le_normalizer (hc.swapHyp hw hn hno) hcs hC hsΛ hne fun x hx =>
      hc.bar_CN_le_normalizer h34 hw hn hno hgen ht (hCN hx)

theorem Ctx.sSup_inf_CN_eq_bot (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {t : G} (ht : t ∈ LB M Q B)
    (𝒮 : Set (Subgroup (Mbar M Q)))
    (h𝒮 : ∀ C ∈ 𝒮, IsComponent C ∧ C ≤ bar M Q (Rt M (LB M Q B) t)) :
    sSup 𝒮 ⊓ bar M Q (hc.CN t) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx𝒮, hxN⟩
  have hxE : x ∈ layer (Mbar M Q) :=
    (sSup_le fun C hC => CFSG.LocalCores.component_le_layer (h𝒮 C hC).1 : sSup 𝒮 ≤ _) hx𝒮
  refine Subgroup.mem_bot.mpr (hcs.eq_one_of_comm_components hxE fun D hD d hd => ?_)
  by_cases hDS : D ∈ 𝒮
  ·
    obtain ⟨-, hDR⟩ := h𝒮 D hDS
    have hxn : x * d * x⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LocalCores.layer_le_normalizer hD hxE) d).mp hd
    have h1 : d * x⁻¹ * d⁻¹ ∈ bar M Q (hc.CN t) := by
      have := hc.bar_CN_conj_mem ht (hDR hd) ((bar M Q (hc.CN t)).inv_mem hxN)
      exact this
    have h2 : (x * d * x⁻¹) * d⁻¹ ∈ D ⊓ bar M Q (hc.CN t) := by
      refine ⟨D.mul_mem hxn (D.inv_mem hd), ?_⟩
      have e : (x * d * x⁻¹) * d⁻¹ = x * (d * x⁻¹ * d⁻¹) := by group
      rw [e]
      exact (bar M Q (hc.CN t)).mul_mem hxN h1
    rw [hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs ht (h𝒮 D hDS).1 hDR,
      Subgroup.mem_bot, mul_inv_eq_one] at h2
    calc d * x = (x * d * x⁻¹) * x := by rw [h2]
      _ = x * d := by group
  · have hle : sSup 𝒮 ≤ Subgroup.centralizer ({d} : Set (Mbar M Q)) := by
      refine sSup_le fun C hC c hc' => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hne : C ≠ D := fun h => hDS (h ▸ hC)
      exact comm_of_ne_component (h𝒮 C hC).1 hD hne c hc' d hd
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx𝒮)).symm


theorem Ctx.exists_lift_ne_one (hc : Ctx M Q Z B) {x : Mbar M Q}
    (hx : x ∈ bar M Q (LB M Q B)) (hx1 : x ≠ 1) :
    ∃ t : ↥M, (t : G) ∈ LB M Q B ∧ (t : G) ∉ Q ∧ (QuotientGroup.mk t : Mbar M Q) = x := by
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hx
  refine ⟨t, ht, fun hq => hx1 ?_, htx⟩
  rw [← htx]
  exact (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_subgroupOf.mpr hq)

theorem Ctx.bar_Lgen_le_normalizer_of_forall (hc : Ctx M Q Z B) {C : Subgroup (Mbar M Q)}
    (hall : ∀ g : Mbar M Q, bar M Q (LB M Q B) ≤
      Subgroup.normalizer (conjSubgroup g C : Set (Mbar M Q))) :
    bar M Q (Lgen M (LB M Q B)) ≤ Subgroup.normalizer (C : Set (Mbar M Q)) := by
  rw [bar_Lgen_eq_normalClosure hc, Subgroup.normalClosure]
  refine (Subgroup.closure_le _).mpr ?_
  intro y hy
  obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨u, hu⟩ := isConj_iff.mp hay
  rw [← hu]
  refine Subgroup.mem_normalizer_fintype fun c hcC => ?_
  have h1 : u⁻¹ * c * u ∈ conjSubgroup u⁻¹ C := by
    rw [mem_conjSubgroup]
    have e0 : (u⁻¹)⁻¹ * (u⁻¹ * c * u) * u⁻¹ = c := by group
    rw [e0]
    exact hcC
  have h2 := (Subgroup.mem_normalizer_iff.mp (hall u⁻¹ ha) _).mp h1
  rw [mem_conjSubgroup] at h2
  have e : (u⁻¹)⁻¹ * (a * (u⁻¹ * c * u) * a⁻¹) * u⁻¹ = u * a * u⁻¹ * c * (u * a * u⁻¹)⁻¹ := by
    group
  rw [e] at h2
  exact h2

end Basic

end CFSG.RankThree.GF2n.Stroth80
