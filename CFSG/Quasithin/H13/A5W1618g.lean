module

public import CFSG.Quasithin.H13.A5W1618f
public import CFSG.Quasithin.Background.C1PackSolvBasic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Solvable

variable {G : Type} [Group G]

theorem eq_of_normal_of_le_sup_solvable {K H N : Subgroup G} (hHK : H ≤ K) (hNK : N ≤ K)
    (hperf : ⁅K, K⁆ = K) (hN : Group.IsSolvable ↥N) (hnorm : (H.subgroupOf K).Normal)
    (hKHN : K ≤ H ⊔ N) : H = K := by
  have hKnorm : K ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hnorm
  let f : ↥(N.subgroupOf K) →* ↥K ⧸ H.subgroupOf K :=
    (QuotientGroup.mk' (H.subgroupOf K)).comp (N.subgroupOf K).subtype
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : G) ∈ ((H ⊔ N : Subgroup G) : Set G) := hKHN x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H N (hNK.trans hKnorm)] at hx
    obtain ⟨h, hh, n, hn, hxhn⟩ := hx
    have hx1 : (x : ↥K) = ⟨h, hHK hh⟩ * ⟨n, hNK hn⟩ := Subtype.ext hxhn.symm
    refine ⟨⟨⟨n, hNK hn⟩, by simpa [Subgroup.mem_subgroupOf] using hn⟩, ?_⟩
    show (QuotientGroup.mk (⟨n, hNK hn⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = QuotientGroup.mk x
    rw [hx1, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨h, hHK hh⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by simpa [Subgroup.mem_subgroupOf] using hh)
    rw [this, one_mul]
  have hN' : Group.IsSolvable ↥(N.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNK).injective
  have hQsolv : Group.IsSolvable (↥K ⧸ H.subgroupOf K) := Group.isSolvable_of_surjective hsurj
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have hQperf : Group.IsPerfect (↥K ⧸ H.subgroupOf K) := inferInstance
  have hsub : Subsingleton (↥K ⧸ H.subgroupOf K) := by
    by_contra hns
    have : Nontrivial (↥K ⧸ H.subgroupOf K) := not_subsingleton_iff_nontrivial.mp hns
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K ⧸ H.subgroupOf K)).ne
      (Group.isPerfect_def.mp hQperf)
  refine le_antisymm hHK fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ H.subgroupOf K) = 1 := Subsingleton.elim _ _
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem eq_of_subnormal_of_le_sup_solvable {A L N : Subgroup G} (hNL : N ≤ L)
    (hperf : ⁅L, L⁆ = L) (hN : Group.IsSolvable ↥N) (hA : IsSubnormal A L) (hLAN : L ≤ A ⊔ N) :
    A = L := by
  induction hA with
  | refl => rfl
  | @step A M K hAM hnorm hMK ih =>
    have hMK' : M = K := ih hNL hperf (hLAN.trans (sup_le_sup_right hAM N))
    subst hMK'
    exact eq_of_normal_of_le_sup_solvable hAM hNL hperf hN hnorm hLAN

end Solvable

theorem mem_cComp_self_of_isQuasisimple {Γ : Type*} [Group Γ] {Q : Subgroup Γ}
    (hq : CFSG.IsQuasisimple ↥Q) : Q ∈ cComp Q := by
  have hnt : Nontrivial ↥Q := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨(Subgroup.nontrivial_iff_ne_bot Q).mp hnt, hperf, IsSubnormal.refl Q,
    fun K' hK'lt hK'ne hK'perf hK'sub => ?_⟩
  have h2 : (K'.subgroupOf Q).IsSubnormal := by
    have := A3.subnormal_comap Q.subtype hK'sub
    have h3 : Q.comap Q.subtype = ⊤ := Subgroup.subgroupOf_self Q
    rw [h3] at this
    exact A3.subnormal_top_iff.mp this
  rcases A3.eq_top_or_le_center_of_subnormal hq h2 with htop | hcenter
  · exact hK'lt.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  · apply hK'ne
    rw [← hK'perf]
    refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
    have hac : (⟨a, hK'lt.le ha⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
      hcenter (Subgroup.mem_subgroupOf.mpr ha)
    have := Subgroup.mem_center_iff.mp hac ⟨b, hK'lt.le hb⟩
    have h4 : b * a = a * b := congrArg Subtype.val this
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr h4.symm)

section RankOne

variable {Γ : Type*} [Group Γ] {L T : Subgroup Γ}

theorem le_borelOf_sup_of_lt (hR : RankOneAt L (T ⊓ L))
    (hTL : T ≤ Subgroup.normalizer (L : Set Γ)) {Y : Subgroup Γ} (hTY : T ≤ Y)
    (hY : Y < L ⊔ T) : Y ≤ borelOf L T ⊔ T := by
  have hYL : Y ⊓ L ≠ L := by
    intro h
    apply hY.ne
    refine le_antisymm hY.le (sup_le ?_ hTY)
    rw [← h]
    exact inf_le_left
  have hle : Y ⊓ L ≤ borelOf L T :=
    le_inf inf_le_right (hR.unique_max (Y ⊓ L) (le_inf (inf_le_left.trans hTY) inf_le_right)
      inf_le_right hYL)
  intro y hy
  have hmul : ((L ⊔ T : Subgroup Γ) : Set Γ) = (L : Set Γ) * (T : Set Γ) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL
  have hy' : y ∈ (L : Set Γ) * (T : Set Γ) := by
    rw [← hmul]
    exact hY.le hy
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hy'
  have hlY : l ∈ Y := by
    have e : l = (l * t) * t⁻¹ := by group
    rw [e]
    exact Y.mul_mem hy (Y.inv_mem (hTY ht))
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hle ⟨hlY, hl⟩)) (Subgroup.mem_sup_right ht)

theorem borelOf_sup_lt (hR : RankOneAt L (T ⊓ L)) (hTL : T ≤ Subgroup.normalizer (L : Set Γ)) :
    borelOf L T ⊔ T < L ⊔ T := by
  refine lt_of_le_of_ne (sup_le_sup inf_le_left le_rfl) fun h => ?_
  apply hR.borel_ne
  refine le_antisymm inf_le_left fun l hl => ?_
  have hlBT : l ∈ ((borelOf L T ⊔ T : Subgroup Γ) : Set Γ) := by
    rw [h]
    exact Subgroup.mem_sup_left hl
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ T (F1.le_normalizer_borelOf hTL)] at hlBT
  obtain ⟨b, hb, t, ht, rfl⟩ := Set.mem_mul.mp hlBT
  have htL : t ∈ L := by
    have e : t = b⁻¹ * (b * t) := by group
    rw [e]
    exact L.mul_mem (L.inv_mem hb.1) hl
  have htN : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        L.mul_mem (L.mul_mem htL hxL) (L.inv_mem htL)⟩
    · rintro ⟨hxT, hxL⟩
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [e]
      exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht,
        L.mul_mem (L.mul_mem (L.inv_mem htL) hxL) htL⟩
  have htB : t ∈ borelOf L T := ⟨htL, htN⟩
  exact (borelOf L T).mul_mem hb htB

theorem isUniqueMaxOver_borelOf_sup (hR : RankOneAt L (T ⊓ L))
    (hTL : T ≤ Subgroup.normalizer (L : Set Γ)) :
    IsUniqueMaxOver (L ⊔ T) T (borelOf L T ⊔ T) := by
  rw [isUniqueMaxOver_iff]
  have hmax : IsMaxSubgroupIn (L ⊔ T) (borelOf L T ⊔ T) := by
    refine ⟨borelOf_sup_lt hR hTL, fun K' hK' hK'X => ?_⟩
    by_contra hne
    exact absurd (le_borelOf_sup_of_lt hR hTL (le_sup_right.trans hK'.le)
      (lt_of_le_of_ne hK'X hne)) (not_le_of_gt hK')
  refine ⟨hmax, le_sup_right, fun N hN hTN => ?_⟩
  have hNle := le_borelOf_sup_of_lt hR hTL hTN hN.1
  by_contra hne
  exact (borelOf_sup_lt hR hTL).ne (hN.2 _ (lt_of_le_of_ne hNle hne) (borelOf_sup_lt hR hTL).le)

theorem not_le_normalizer_of_rankOneAt (hR : RankOneAt L (T ⊓ L)) :
    ¬ L ⊔ T ≤ Subgroup.normalizer (T : Set Γ) := by
  intro h
  apply hR.borel_ne
  refine le_antisymm inf_le_left fun l hl => ⟨hl, ?_⟩
  have hlT : l ∈ Subgroup.normalizer (T : Set Γ) := h (Subgroup.mem_sup_left hl)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hlT, Subgroup.le_normalizer hl⟩

end RankOne

variable {G : Type} [Group G] [Finite G]

theorem mem_lFamily_of_autOn {B T W : Subgroup G} (hBp : ⁅B, B⁆ = B)
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hker : Group.IsSolvable ↥(B ⊓ Subgroup.centralizer (W : Set G)))
    (hQ : autOn B W ∈ cComp (autOn B W)) : B ∈ lFamily T := by
  have hne : B ≠ ⊥ := by
    rintro rfl
    apply ne_bot_of_mem_cComp hQ
    unfold autOn
    simp
  refine ⟨hne, hBp, A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTB)), fun L hLB hLne hLp hLsub => ?_⟩
  have hLsubB : IsSubnormal L B := A3.subnormal_of_le_of_le hLsub hLB.le le_sup_left
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hLB.le.trans hBW
  have himsub : IsSubnormal (autOn L W) (autOn B W) := A4.autOn_subnormal hLsubB
  have himp : ⁅autOn L W, autOn L W⁆ = autOn L W := by
    rw [← CFSG.Quasithin.H13.A5.autOn_commutator hLW hLW, hLp]
  by_cases him : autOn L W = autOn B W
  ·
    apply hLB.ne
    refine eq_of_subnormal_of_le_sup_solvable inf_le_left hBp hker hLsubB fun b hb => ?_
    have hbim : conjAct W ⟨b, hBW hb⟩ ∈ autOn L W := by
      rw [him]
      exact Setup.mem_autOn_iff.2 ⟨⟨b, hBW hb⟩, hb, rfl⟩
    obtain ⟨⟨l, hlN⟩, hl, hlb⟩ := Setup.mem_autOn_iff.1 hbim
    have hc : l⁻¹ * b ∈ Subgroup.centralizer (W : Set G) := by
      have h1 : conjAct W ((⟨l, hlN⟩ : ↥(Subgroup.normalizer (W : Set G)))⁻¹ * ⟨b, hBW hb⟩) =
          1 := by
        rw [map_mul, map_inv, hlb, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.mp h1
    have e : b = l * (l⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
      (Subgroup.mem_sup_right ⟨B.mul_mem (B.inv_mem (hLB.le hl)) hb, hc⟩)
  · have hlt : autOn L W < autOn B W := lt_of_le_of_ne (A4.autOn_mono hLB.le) him
    by_cases hbot : autOn L W = ⊥
    ·
      apply hLne
      have hLC : L ≤ B ⊓ Subgroup.centralizer (W : Set G) :=
        le_inf hLB.le ((autOn_eq_bot_iff hLW).mp hbot)
      have hs : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hLC) (Subgroup.inclusion_injective hLC)
      have h1 := (isSolvable_iff_perfectCore_eq_bot L).mp hs
      rwa [perfectCore_eq_self_of_perfect hLp] at h1
    · exact not_subnormal_of_mem_cComp hQ hlt hbot himp himsub

theorem exists_minParabolic_member {K T W : Subgroup G} {Mst : Subgroup (MulAut ↥W)}
    (hKp : ⁅K, K⁆ = K) (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hT : IsSylowTwoOf T (K ⊔ T))
    (hker : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (W : Set G)))
    (hQ : autOn K W ∈ cComp (autOn K W))
    (hM : IsUniqueMaxOver (autOn (K ⊔ T) W) (autOn T W) Mst)
    (hnn : ¬ autOn (K ⊔ T) W ≤
      Subgroup.normalizer ((autOn T W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W))) :
    ∃ K₀ : Subgroup G,
      Minimal (fun B : Subgroup G => B ≤ K ∧ B ∈ lFamily T ∧
        T ≤ Subgroup.normalizer (B : Set G) ∧ autOn B W = autOn K W) K₀ ∧
      MinParabolic (K₀ ⊔ T) T
        ((K₀ ⊔ T) ⊓ (Mst.comap (conjAct W)).map (Subgroup.normalizer (W : Set G)).subtype) := by
  classical
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  obtain ⟨K₀, -, hK₀⟩ := exists_minimal_le_of_wellFoundedLT (fun B : Subgroup G => B ≤ K ∧
    B ∈ lFamily T ∧ T ≤ Subgroup.normalizer (B : Set G) ∧ autOn B W = autOn K W) K
    ⟨le_rfl, mem_lFamily_of_autOn hKp hKW hTK hker hQ, hTK, rfl⟩
  refine ⟨K₀, hK₀, ?_⟩
  obtain ⟨⟨hK₀K, hK₀L, hTK₀, hK₀im⟩, hmin⟩ := hK₀
  have hK₀W : K₀ ≤ Subgroup.normalizer (W : Set G) := hK₀K.trans hKW
  have hQp : ⁅autOn K W, autOn K W⁆ = autOn K W := perfect_of_mem_cComp hQ
  have hHim : autOn (K₀ ⊔ T) W = autOn (K ⊔ T) W := by
    rw [CFSG.Quasithin.H13.A5.autOn_sup hK₀W hTW, CFSG.Quasithin.H13.A5.autOn_sup hKW hTW, hK₀im]
  have hkey : ∀ Y : Subgroup G, T ≤ Y → Y ≤ K₀ ⊔ T → autOn K W ≤ autOn Y W → Y = K₀ ⊔ T := by
    intro Y hTY hYH hQY
    have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYH.trans (sup_le hK₀W hTW)
    have hY₀W : Y ⊓ K₀ ≤ Subgroup.normalizer (W : Set G) := inf_le_left.trans hYW
    have hYK₀ : Y ≤ Subgroup.normalizer (K₀ : Set G) :=
      hYH.trans (sup_le Subgroup.le_normalizer hTK₀)
    have hYY₀ : Y ≤ Subgroup.normalizer ((Y ⊓ K₀ : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hYK₀ hy⟩
    have hQY₀ : autOn K W ≤ autOn (Y ⊓ K₀) W := by
      refine (le_twoResidual_of_perfect hQp hQY).trans ?_
      refine twoResidual_le_of_isTwoQuotient (A4.autOn_mono inf_le_left)
        (CFSG.Quasithin.H13.A5.autOn_le_normalizer_autOn hYY₀) fun x hx => ?_
      obtain ⟨⟨y, hyN⟩, hyY, rfl⟩ := Setup.mem_autOn_iff.1 hx
      obtain ⟨k, hk⟩ := C1.exists_pow_mem_of_mem_sup hT2 hTK₀ (hYH hyY)
      refine ⟨k, Setup.mem_autOn_iff.2 ⟨⟨y, hyN⟩ ^ 2 ^ k, ⟨?_, ?_⟩, by rw [map_pow]⟩⟩
      · rw [Subgroup.coe_pow]
        exact Y.pow_mem hyY _
      · rw [Subgroup.coe_pow]
        exact hk
    have hY₁W : perfectCore (Y ⊓ K₀) ≤ Subgroup.normalizer (W : Set G) :=
      (perfectCore_le _).trans hY₀W
    have hY₁K₀ : perfectCore (Y ⊓ K₀) ≤ K₀ := (perfectCore_le _).trans inf_le_right
    have hTY₁ : T ≤ Subgroup.normalizer (perfectCore (Y ⊓ K₀) : Set G) :=
      (hTY.trans hYY₀).trans (normalizer_le_normalizer_perfectCore _)
    have hY₁im : autOn (perfectCore (Y ⊓ K₀)) W = autOn K W := by
      refine le_antisymm ((A4.autOn_mono hY₁K₀).trans hK₀im.le) ?_
      rw [Vol2.Ch11.SecA.autOn_perfectCore hY₀W]
      exact le_perfectCore_of_perfect hQY₀ hQp
    have hY₁ker : Group.IsSolvable
        ↥(perfectCore (Y ⊓ K₀) ⊓ Subgroup.centralizer (W : Set G)) := by
      have hle : perfectCore (Y ⊓ K₀) ⊓ Subgroup.centralizer (W : Set G) ≤
          K ⊓ Subgroup.centralizer (W : Set G) := inf_le_inf_right _ (hY₁K₀.trans hK₀K)
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    have hY₁P : perfectCore (Y ⊓ K₀) ≤ K ∧ perfectCore (Y ⊓ K₀) ∈ lFamily T ∧
        T ≤ Subgroup.normalizer (perfectCore (Y ⊓ K₀) : Set G) ∧
        autOn (perfectCore (Y ⊓ K₀)) W = autOn K W :=
      ⟨hY₁K₀.trans hK₀K, mem_lFamily_of_autOn (perfectCore_perfect _) hY₁W hTY₁ hY₁ker
        (hY₁im ▸ hQ), hTY₁, hY₁im⟩
    have hY₁eq : perfectCore (Y ⊓ K₀) = K₀ := le_antisymm hY₁K₀ (hmin hY₁P hY₁K₀)
    refine le_antisymm hYH (sup_le ?_ hTY)
    rw [← hY₁eq]
    exact (perfectCore_le _).trans inf_le_left
  obtain ⟨hMmax, hTM, hMuniq⟩ := isUniqueMaxOver_iff.mp hM
  have hle_pre : ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (W : Set G) → autOn Y W ≤ Mst →
      Y ≤ (Mst.comap (conjAct W)).map (Subgroup.normalizer (W : Set G)).subtype :=
    fun Y hYW hY y hy => ⟨⟨y, hYW hy⟩, hY (Setup.mem_autOn_iff.2 ⟨⟨y, hYW hy⟩, hy, rfl⟩), rfl⟩
  refine C1Pack.minParabolic_of_minimal (B6.isSylowTwoOf_mono hT le_sup_right
    (sup_le_sup_right hK₀K T)) (hle_pre T hTW hTM) (fun h => ?_) (fun P' hTP' hP'lt => ?_)
    fun h => ?_
  ·
    apply hMmax.1.not_ge
    rw [← hHim]
    intro x hx
    obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := Setup.mem_autOn_iff.1 hx
    obtain ⟨⟨g', hg'N⟩, hg', rfl⟩ := h hg
    exact hg'
  ·
    have hP'W : P' ≤ Subgroup.normalizer (W : Set G) := hP'lt.le.trans (sup_le hK₀W hTW)
    refine hle_pre P' hP'W ?_
    have hne : autOn P' W ≠ autOn (K ⊔ T) W := by
      intro h
      apply hP'lt.ne
      apply hkey P' hTP' hP'lt.le
      rw [h]
      exact A4.autOn_mono le_sup_left
    have hlt : autOn P' W < autOn (K ⊔ T) W :=
      lt_of_le_of_ne (hHim ▸ A4.autOn_mono hP'lt.le) hne
    obtain ⟨N, hN, hP'N⟩ := exists_isMaxSubgroupIn hlt
    rw [hMuniq N hN ((A4.autOn_mono hTP').trans hP'N)] at hP'N
    exact hP'N
  ·
    apply hnn
    rw [← hHim]
    exact CFSG.Quasithin.H13.A5.autOn_le_normalizer_autOn h

end CFSG.Quasithin.H13.A5
