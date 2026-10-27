module

public import CFSG.Quasithin.EmptyFaithful.S151bModule
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_hom_eq_one_of_perfect {G M : Type*} [Group G] [Group M]
    [IsMulCommutative M] (hG : commutator G = ⊤) (f : G →* M) : f = 1 := by
  have hle : commutator G ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' (f a) (f b)
  rw [hG] at hle
  ext g
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

private theorem s16h_normal_le_center_or_eq_top {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hQ
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hsimple
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' _
  have hnorm : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  · left
    intro x hx
    have hmem : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    simpa [π] using hmem
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have h := Subgroup.comap_map_eq π N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hder : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hder
    exact top_unique hder

private theorem s16h_commutatorElement_mul_central {G : Type*} [Group G]
    (c d : Subgroup.center G) (a b : G) :
    ⁅(c : G) * a, (d : G) * b⁆ = ⁅a, b⁆ := by
  have hc : ∀ x : G, (c : G) * x = x * (c : G) :=
    fun x => (Subgroup.mem_center_iff.mp c.2 x).symm
  have hd : ∀ x : G, (d : G) * x = x * (d : G) :=
    fun x => (Subgroup.mem_center_iff.mp d.2 x).symm
  have hcd : ⁅(c : G), (d : G) * b⁆ = 1 := by
    have hmem : ⁅(c : G), (d : G) * b⁆ ∈ ⁅Subgroup.center G, (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator c.2 (Subgroup.mem_top _)
    rw [Subgroup.commutator_center_left] at hmem
    exact Subgroup.mem_bot.mp hmem
  have had : ⁅a, (d : G)⁆ = 1 := by
    have hmem : ⁅a, (d : G)⁆ ∈ ⁅(⊤ : Subgroup G), Subgroup.center G⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) d.2
    rw [Subgroup.commutator_center_right] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj]
  rw [hcd, had, one_mul, mul_one]
  rw [show (d : G) * ⁅a, b⁆ * (d : G)⁻¹ = ⁅a, b⁆ by rw [hd ⁅a, b⁆]; group,
      show (c : G) * ⁅a, b⁆ * (c : G)⁻¹ = ⁅a, b⁆ by rw [hc ⁅a, b⁆]; group]

private theorem s16h_commSub_commSub_eq (L : Subgroup (MulAut W))
    (hperf : commutator ↥L = ⊤) :
    commSub (commSub ⊤ L) L = commSub ⊤ L := by
  set U : Subgroup W := commSub ⊤ L with hU
  set K4 : Subgroup W := commSub U L with hK4
  have hLstab : ∀ l ∈ L, ∀ w ∈ U, l w ∈ U := by
    intro l hl w hw
    rw [hU] at hw ⊢
    exact commSub_top_stable151b
      (fun l' hl' => L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl)) w hw
  have hle : K4 ≤ U := by
    rw [hK4]
    exact commSub_le_of_invariant (fun l hl w hw => hLstab l hl w hw)
  have key : ∀ w : W, ∀ l ∈ L, l w * w⁻¹ ∈ K4 := by
    intro w l hl
    let g : ↥L →* W ⧸ K4 :=
      { toFun := fun a => QuotientGroup.mk' K4 ((a : MulAut W) w * w⁻¹)
        map_one' := by simp
        map_mul' := fun a b => by
          have hgen : (a : MulAut W) ((b : MulAut W) w * w⁻¹) *
              ((b : MulAut W) w * w⁻¹)⁻¹ ∈ K4 :=
            Subgroup.subset_closure ⟨(a : MulAut W), a.2,
              (b : MulAut W) w * w⁻¹,
              Subgroup.subset_closure ⟨(b : MulAut W), b.2, w, Subgroup.mem_top w, rfl⟩, rfl⟩
          have hstep : QuotientGroup.mk' K4 ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) =
              QuotientGroup.mk' K4 ((b : MulAut W) w * w⁻¹) := by
            have h1 : QuotientGroup.mk' K4 ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) *
                (QuotientGroup.mk' K4 ((b : MulAut W) w * w⁻¹))⁻¹ = 1 := by
              rw [← map_inv, ← map_mul]
              exact (QuotientGroup.eq_one_iff _).mpr hgen
            exact mul_inv_eq_one.mp h1
          have hid : ((a : MulAut W) * (b : MulAut W)) w * w⁻¹ =
              ((a : MulAut W) w * w⁻¹) *
                ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) := by
            have ha : (a : MulAut W) ((b : MulAut W) w * w⁻¹) =
                (a : MulAut W) ((b : MulAut W) w) * ((a : MulAut W) w)⁻¹ := by
              rw [map_mul, map_inv]
            rw [ha]
            simp only [MulAut.mul_apply]
            calc (a : MulAut W) ((b : MulAut W) w) * w⁻¹ =
                (((a : MulAut W) w) * ((a : MulAut W) w)⁻¹) *
                  ((a : MulAut W) ((b : MulAut W) w) * w⁻¹) := by
                  rw [mul_inv_cancel, one_mul]
              _ = ((a : MulAut W) w * w⁻¹) *
                  ((a : MulAut W) ((b : MulAut W) w) * ((a : MulAut W) w)⁻¹) := by ac_rfl
          change QuotientGroup.mk' K4 (((a : MulAut W) * (b : MulAut W)) w * w⁻¹) =
              QuotientGroup.mk' K4 ((a : MulAut W) w * w⁻¹) *
                QuotientGroup.mk' K4 ((b : MulAut W) w * w⁻¹)
          rw [hid, map_mul, hstep] }
    have hg : g = 1 := s16h_hom_eq_one_of_perfect hperf g
    have happ : g ⟨l, hl⟩ = 1 := by rw [hg]; rfl
    exact (QuotientGroup.eq_one_iff _).mp happ
  have hge : U ≤ K4 := by
    rw [hU, commSub, Subgroup.closure_le]
    rintro c ⟨l, hl, w, -, rfl⟩
    exact key w l hl
  exact le_antisymm hle hge

theorem s16h_H5_triv_of_triv_quot {A L : Subgroup (MulAut W)} (hcomp : IsComponentOf L A)
    {x : MulAut W} (hx : x ∈ normalizer (L : Set (MulAut W)))
    (hxq : ∀ w ∈ commSub ⊤ L, x w * w⁻¹ ∈ commSub ⊤ L ⊓ fixV L) :
    ∀ w ∈ commSub ⊤ L, x w = w := by
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := U ⊓ fixV L with hZ
  have hLq : CFSG.Open.IsQuasisimple ↥L := hcomp.2.2
  have hLperf : commutator ↥L = ⊤ := hLq.1
  have hxnorm : ∀ l ∈ L, x * l * x⁻¹ ∈ L :=
    fun l hl => (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hxinvnorm : ∀ l ∈ L, x⁻¹ * l * (x⁻¹)⁻¹ ∈ L :=
    fun l hl =>
      (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hx) l).mp hl
  have hxU : ∀ u ∈ U, x u ∈ U := by
    intro u hu
    rw [hU] at hu ⊢
    exact commSub_top_stable151b hxnorm u hu
  have hxinvU : ∀ u ∈ U, x⁻¹ u ∈ U := by
    intro u hu
    rw [hU] at hu ⊢
    exact commSub_top_stable151b hxinvnorm u hu
  have hLU : ∀ l : ↥L, ∀ u : U, (l : MulAut W) u.1 ∈ U := by
    intro l u
    have hmem : u.1 ∈ commSub ⊤ L := by rw [← hU]; exact u.2
    have h := commSub_top_stable151b
      (fun l' hl' => L.mul_mem (L.mul_mem l.2 hl') (L.inv_mem l.2)) u.1 hmem
    rwa [← hU] at h
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hLne : L ≠ ⊥ := by
      intro hLbot
      haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hLq.2.toNontrivial
      haveI hnt : Nontrivial ↥L :=
        (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot L).mp hnt hLbot
    have hsub : commSub ⊤ L = ⊥ := by rw [← hU]; exact hbot
    have hfix : fixV L = ⊤ := by
      rw [eq_top_iff]
      intro w _
      exact commSub_eq_bot_iff.mp hsub (Subgroup.mem_top w)
    apply hLne
    apply le_bot_iff.mp
    intro l hl
    rw [Subgroup.mem_bot]
    exact MulEquiv.ext (fun w => mem_fixV.mp (hfix.symm ▸ Subgroup.mem_top w) l hl)
  set Y : Subgroup W := Subgroup.closure
    ({c : W | ∃ u ∈ U, x u * u⁻¹ = c} ∪ {c : W | ∃ u ∈ U, x⁻¹ u * u⁻¹ = c}) with hY
  have hxY : ∀ u ∈ U, x u * u⁻¹ ∈ Y := fun u hu =>
    Subgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩)
  have hxinvY : ∀ u ∈ U, x⁻¹ u * u⁻¹ ∈ Y := fun u hu =>
    Subgroup.subset_closure (Or.inr ⟨u, hu, rfl⟩)
  have hYU : Y ≤ U := by
    rw [hY, Subgroup.closure_le]
    rintro c (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact U.mul_mem (hxU u hu) (U.inv_mem hu)
    · exact U.mul_mem (hxinvU u hu) (U.inv_mem hu)
  have hYZ : Y ≤ Z := by
    rw [hY, Subgroup.closure_le]
    rintro c (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · have h := hxq u (hU ▸ hu)
      rwa [hZ]
    · have hu' : x⁻¹ u ∈ U := hxinvU u hu
      have h := hxq (x⁻¹ u) (hU ▸ hu')
      have h2 : x (x⁻¹ u) = u := by simp
      rw [h2] at h
      have := (U ⊓ fixV L).inv_mem h
      rw [hZ]
      simpa [mul_inv_rev, inv_inv] using this
  have hfixY : ∀ l ∈ L, ∀ y ∈ Y, l y = y := by
    intro l hl y hy
    have hyZ : y ∈ U ⊓ fixV L := hZ ▸ hYZ hy
    exact mem_fixV.mp hyZ.2 l hl
  let K : Subgroup ↥L :=
    { carrier := {l | ∀ u : U, (l : MulAut W) u.1 * u.1⁻¹ ∈ Y}
      one_mem' := by
        intro u
        simp
      mul_mem' := by
        intro a b ha hb u
        have hb' : (b : MulAut W) u.1 * u.1⁻¹ ∈ Y := hb u
        have ha' : (a : MulAut W) u.1 * u.1⁻¹ ∈ Y := ha u
        have hfix : (a : MulAut W) ((b : MulAut W) u.1 * u.1⁻¹) =
            (b : MulAut W) u.1 * u.1⁻¹ := hfixY a a.2 _ hb'
        change (a : MulAut W) ((b : MulAut W) u.1) * u.1⁻¹ ∈ Y
        have hcalc : (a : MulAut W) ((b : MulAut W) u.1) * u.1⁻¹ =
            ((b : MulAut W) u.1 * u.1⁻¹) * ((a : MulAut W) u.1 * u.1⁻¹) := by
          calc (a : MulAut W) ((b : MulAut W) u.1) * u.1⁻¹
              = (a : MulAut W) (((b : MulAut W) u.1 * u.1⁻¹) * u.1) * u.1⁻¹ := by
                rw [show ((b : MulAut W) u.1 * u.1⁻¹) * u.1 = (b : MulAut W) u.1 by group]
            _ = ((a : MulAut W) ((b : MulAut W) u.1 * u.1⁻¹)) *
                  ((a : MulAut W) u.1) * u.1⁻¹ := by rw [map_mul]
            _ = ((b : MulAut W) u.1 * u.1⁻¹) * ((a : MulAut W) u.1) * u.1⁻¹ := by rw [hfix]
            _ = ((b : MulAut W) u.1 * u.1⁻¹) * ((a : MulAut W) u.1 * u.1⁻¹) := by group
        rw [hcalc]
        exact Y.mul_mem hb' ha'
      inv_mem' := by
        intro a ha u
        have hv : ((a⁻¹ : ↥L) : MulAut W) u.1 ∈ U := hLU a⁻¹ u
        have hmem := ha ⟨((a⁻¹ : ↥L) : MulAut W) u.1, hv⟩
        have h2 : (a : MulAut W) (((a⁻¹ : ↥L) : MulAut W) u.1) = u.1 := by simp
        rw [h2] at hmem
        have := Y.inv_mem hmem
        simpa [mul_inv_rev, inv_inv] using this }
  have hKnormal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    intro u
    have hv : ((g⁻¹ : ↥L) : MulAut W) u.1 ∈ U := hLU g⁻¹ u
    have hmem := hn ⟨((g⁻¹ : ↥L) : MulAut W) u.1, hv⟩
    have hfix : (g : MulAut W) ((n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) *
        (((g⁻¹ : ↥L) : MulAut W) u.1)⁻¹) =
        (n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) *
        (((g⁻¹ : ↥L) : MulAut W) u.1)⁻¹ := hfixY g g.2 _ hmem
    change (g : MulAut W) ((n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1)) * u.1⁻¹ ∈ Y
    have h1 : (g : MulAut W) ((n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1)) =
        ((n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) *
          (((g⁻¹ : ↥L) : MulAut W) u.1)⁻¹) * u.1 := by
      rw [show (n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) =
          ((n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) *
            (((g⁻¹ : ↥L) : MulAut W) u.1)⁻¹) * (((g⁻¹ : ↥L) : MulAut W) u.1) by group]
      rw [map_mul, hfix]
      simp
    rw [h1]
    have h2 : ((n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) *
          (((g⁻¹ : ↥L) : MulAut W) u.1)⁻¹) * u.1 * u.1⁻¹ =
        (n : MulAut W) (((g⁻¹ : ↥L) : MulAut W) u.1) *
          (((g⁻¹ : ↥L) : MulAut W) u.1)⁻¹ := by group
    rw [h2]
    exact hmem
  have hKne : K ≠ ⊤ := by
    intro hKtop
    have hle : commSub U L ≤ Y := by
      rw [commSub, Subgroup.closure_le]
      rintro c ⟨l, hl, u, hu, rfl⟩
      have hmem : (⟨l, hl⟩ : ↥L) ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
      exact hmem ⟨u, hu⟩
    have h4 : commSub U L = U := by rw [hU]; exact s16h_commSub_commSub_eq L hLperf
    have hUleY : U ≤ Y := h4 ▸ hle
    have hUeqZ : U = Z := le_antisymm (hUleY.trans hYZ) (by rw [hZ]; exact inf_le_left)
    have hcomm_bot : commSub U L = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro u hu
      rw [mem_fixV]
      intro l hl
      have huZ : u ∈ Z := hUeqZ ▸ hu
      exact mem_fixV.mp (hZ ▸ huZ).2 l hl
    rw [h4] at hcomm_bot
    exact hUne hcomm_bot
  have hKcenter : K ≤ Subgroup.center ↥L := by
    haveI : K.Normal := hKnormal
    rcases s16h_normal_le_center_or_eq_top hLq K with h | h
    · exact h
    · exact absurd h hKne
  let cx : ↥L →* ↥L :=
    { toFun := fun l => ⟨x * (l : MulAut W) * x⁻¹, hxnorm l.1 l.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  let d : ↥L → ↥L := fun l => cx l * l⁻¹
  have hdK : ∀ l : ↥L, d l ∈ K := by
    intro l
    intro u
    have hv : ((l⁻¹ : ↥L) : MulAut W) u.1 ∈ U := hLU l⁻¹ u
    have h1 : x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1) *
        (((l⁻¹ : ↥L) : MulAut W) u.1)⁻¹ ∈ Y := hxinvY _ hv
    have h2 : (l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1)) * u.1⁻¹ ∈ Y := by
      have hfix := hfixY l l.2 _ h1
      have hmem : (l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1) *
          (((l⁻¹ : ↥L) : MulAut W) u.1)⁻¹) ∈ Y := by rw [hfix]; exact h1
      rw [map_mul, map_inv] at hmem
      have hlv : (l : MulAut W) (((l⁻¹ : ↥L) : MulAut W) u.1) = u.1 := by simp
      rw [hlv] at hmem
      exact hmem
    have hw1 : x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1) ∈ U := hxinvU _ hv
    have h3 : x ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1))) *
        ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1)))⁻¹ ∈ Y :=
      hxY _ (hLU l ⟨_, hw1⟩)
    change x ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1))) * u.1⁻¹ ∈ Y
    have hcalc : x ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1))) * u.1⁻¹ =
        (x ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1))) *
          ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1)))⁻¹) *
          ((l : MulAut W) (x⁻¹ (((l⁻¹ : ↥L) : MulAut W) u.1)) * u.1⁻¹) := by group
    rw [hcalc]
    exact Y.mul_mem h3 h2
  have hdcent : ∀ l : ↥L, d l ∈ Subgroup.center ↥L := fun l => hKcenter (hdK l)
  have hxcent : ∀ l ∈ L, x * l * x⁻¹ = l := by
    have hfix_comm : ∀ a b : ↥L, cx ⁅a, b⁆ = ⁅a, b⁆ := by
      intro a b
      have ha : d a * a = cx a := by
        change cx a * a⁻¹ * a = cx a
        group
      have hb : d b * b = cx b := by
        change cx b * b⁻¹ * b = cx b
        group
      calc cx ⁅a, b⁆ = ⁅cx a, cx b⁆ := map_commutatorElement cx a b
        _ = ⁅d a * a, d b * b⁆ := by rw [← ha, ← hb]
        _ = ⁅a, b⁆ :=
            s16h_commutatorElement_mul_central ⟨d a, hdcent a⟩ ⟨d b, hdcent b⟩ a b
    have hcx : ∀ l : ↥L, cx l = l := by
      intro l
      have hl : l ∈ commutator ↥L := by rw [hLperf]; exact Subgroup.mem_top l
      rw [commutator_eq_closure] at hl
      induction hl using Subgroup.closure_induction with
      | mem c hc =>
          rw [mem_commutatorSet_iff] at hc
          obtain ⟨a, b, rfl⟩ := hc
          exact hfix_comm a b
      | one => exact map_one cx
      | mul a b _ _ iha ihb => rw [map_mul, iha, ihb]
      | inv a _ iha => rw [map_inv, iha]
    intro l hl
    exact congrArg Subtype.val (hcx ⟨l, hl⟩)
  let ψ : U →* W :=
    { toFun := fun u => x u.1 * u.1⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        change x (a.1 * b.1) * (a.1 * b.1)⁻¹ =
          (x a.1 * a.1⁻¹) * (x b.1 * b.1⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hpsi_orbit : ∀ (l : ↥L) (u : U),
      ψ ⟨(l : MulAut W) u.1, hLU l u⟩ = ψ u := by
    intro l u
    have hcomm : x * (l : MulAut W) = (l : MulAut W) * x := by
      have h := hxcent (l : MulAut W) l.2
      calc x * (l : MulAut W) = (x * (l : MulAut W) * x⁻¹) * x := by group
        _ = (l : MulAut W) * x := by rw [h]
    have hxlu : x ((l : MulAut W) u.1) = (l : MulAut W) (x u.1) := by
      calc x ((l : MulAut W) u.1) = (x * (l : MulAut W)) u.1 := rfl
        _ = ((l : MulAut W) * x) u.1 := by rw [hcomm]
        _ = (l : MulAut W) (x u.1) := rfl
    have hfix : (l : MulAut W) (x u.1 * u.1⁻¹) = x u.1 * u.1⁻¹ :=
      hfixY (l : MulAut W) l.2 _ (hxY u.1 u.2)
    change x ((l : MulAut W) u.1) * ((l : MulAut W) u.1)⁻¹ = x u.1 * u.1⁻¹
    rw [hxlu, ← map_inv, ← map_mul]
    exact hfix
  have h4 : commSub U L = U := by rw [hU]; exact s16h_commSub_commSub_eq L hLperf
  have hK4U : commSub U L ≤ U := le_of_eq h4
  have hU4 : U ≤ commSub U L := le_of_eq h4.symm
  have hgen : ∀ c (hc : c ∈ commSub U L), ψ ⟨c, hK4U hc⟩ = 1 := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem d hd =>
        obtain ⟨l, hl, w, hw, rfl⟩ := hd
        have hprod : (⟨l w * w⁻¹, hK4U (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩)⟩ : U) =
            ⟨l w, hLU ⟨l, hl⟩ ⟨w, hw⟩⟩ * ⟨w, hw⟩⁻¹ := Subtype.ext rfl
        rw [hprod, map_mul, map_inv, hpsi_orbit ⟨l, hl⟩ ⟨w, hw⟩]
        group
    | one =>
        rw [show (⟨1, hK4U (commSub U L).one_mem⟩ : U) = 1 from Subtype.ext rfl, map_one]
    | mul a b ha hb iha ihb =>
        rw [show (⟨a * b, hK4U ((commSub U L).mul_mem ha hb)⟩ : U) =
            ⟨a, hK4U ha⟩ * ⟨b, hK4U hb⟩ from Subtype.ext rfl, map_mul, iha, ihb, mul_one]
    | inv a ha iha =>
        rw [show (⟨a⁻¹, hK4U ((commSub U L).inv_mem ha)⟩ : U) =
            (⟨a, hK4U ha⟩ : U)⁻¹ from Subtype.ext rfl, map_inv, iha, inv_one]
  intro w hw
  have hwU : w ∈ U := hw
  have hc : w ∈ commSub U L := h4.symm ▸ hwU
  have h1 : ψ ⟨w, hwU⟩ = 1 := by
    have h := hgen w hc
    rwa [show (⟨w, hK4U hc⟩ : U) = ⟨w, hwU⟩ from Subtype.ext rfl] at h
  exact mul_inv_eq_one.mp h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
