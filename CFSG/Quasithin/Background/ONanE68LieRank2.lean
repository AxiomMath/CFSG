module

public import CFSG.Quasithin.Background.ONanE68LieCase1

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Residual

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_residual_le {X B : Subgroup G} (hB : Group.IsSolvable ↥B)
    (hRB : twoPrimeResidual X ≤ B) : Group.IsSolvable ↥X := by
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf X
  have hcl : conjClosure S X = twoPrimeResidual X := conjClosure_eq_twoPrimeResidual hS
  have hXN : X ≤ Subgroup.normalizer (twoPrimeResidual X : Set G) :=
    hcl ▸ le_normalizer_conjClosure S X
  have hRX : twoPrimeResidual X ≤ X := twoPrimeResidual_le_self X
  have hnorm : ((twoPrimeResidual X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have h1 : Group.IsSolvable ↥((twoPrimeResidual X).subgroupOf X) := by
    have hRB' : Group.IsSolvable ↥(twoPrimeResidual X) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hRB)
        (Subgroup.inclusion_injective hRB)
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRX).symm.surjective
  have h2 : Group.IsSolvable (↥X ⧸ (twoPrimeResidual X).subgroupOf X) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have hodd := odd_relIndex_twoPrimeResidual X
    show Odd ((twoPrimeResidual X).relIndex X)
    exact Nat.odd_iff.2 (by omega)
  have hker : (QuotientGroup.mk' ((twoPrimeResidual X).subgroupOf X)).ker ≤
      ((twoPrimeResidual X).subgroupOf X).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  exact Group.isSolvable_of_ker_le_range _ _ hker

end Residual

section Lin3

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem inf_le_borOf_of_residual (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ pgOf T V L)
    (hPX : pgOf T V L ≤ L ⊓ M) (hXne : L ⊓ M ≠ L) (hBX : borOf T V L ≤ M)
    (hsolvB : Group.IsSolvable ↥(borOf T V L))
    (hres : twoPrimeResidual (L ⊓ M) ≤ borOf T V L)
    (hns : ∀ Y : Subgroup (Bar.Qbar L),
      Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)) < Y → Y ≠ ⊤ →
        ¬ Group.IsSolvable ↥Y) : L ⊓ M ≤ borOf T V L := by
  by_contra hnle
  have hZX : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ L ⊓ M := fun z hz => hPX (hZ z hz)
  have hXsolv : Group.IsSolvable ↥(L ⊓ M) := isSolvable_of_residual_le hsolvB hres
  set Y : Subgroup (Bar.Qbar L) := ((L ⊓ M).subgroupOf L).map (piBar L) with hY
  have hpre : Fin257.pre (piBar L) Y = L ⊓ M := pre_img_eq inf_le_left hZX
  have hYsolv : Group.IsSolvable ↥Y := by
    have : Group.IsSolvable ↥((L ⊓ M).subgroupOf L) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : L ⊓ M ≤ L)).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ M ≤ L)).symm.surjective
    exact Group.isSolvable_of_surjective (f := MonoidHom.subgroupMap (piBar L) _)
      (MonoidHom.subgroupMap_surjective _ _)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply hXne
    rw [htop, Fin257.pre_top] at hpre
    exact hpre.symm
  have hle : Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)) ≤ Y := by
    intro x hx
    obtain ⟨y, hyB, rfl⟩ := exists_mem_borOf_of_mem_normalizer hZ hx
    have hyL : y ∈ L := borOf_le_left hyB
    rw [piG_of_mem hyL]
    exact ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 ⟨hyL, hBX hyB⟩, rfl⟩
  have hne : Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L)) ≠ Y := by
    intro heq
    apply hnle
    intro x hx
    have hxL : x ∈ L := hx.1
    have hxY : piBar L ⟨x, hxL⟩ ∈ Y := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [← heq] at hxY
    exact (mem_borOf_iff hZ).2 ⟨hxL, hxY⟩
  exact hns Y (lt_of_le_of_ne hle hne) hYtop hYsolv

theorem centralizer_le_borOf_of_root (hInn : Ch1.EvenLieAutInner)
    (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L)) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hcr : ∀ g ∈ omegaCenter (sylowBar T V L), g ≠ 1 → ∀ y : Bar.Qbar L, y * g = g * y →
      y ∈ Subgroup.normalizer (sylowBar T V L : Set (Bar.Qbar L))) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ borOf T V L := by
  have hZ := center_le_sylow h hU hL hZ2
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hZ0 := center_qbar_eq_bot hq
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  obtain ⟨θ, hθ, hθZ⟩ := exists_theta hInn hmod h hU hL
  have hne : θ.range ≠ ⊥ :=
    theta_range_ne_bot h.isPGroup_V hVN θ hθ hZ0 hperf (mQuot_ne_zero_of_not_le h hLM)
  obtain ⟨⟨w, a, rfl⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  rintro y ⟨hyL, hyC⟩
  have hcomm : (y : G) * a = a * y := (Subgroup.mem_centralizer_iff.1 hyC a a.2).symm
  have h1 := theta_comm_of_comm hVN θ hθ ⟨y, hyL⟩ a hcomm
  have hg1 : θ a ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
  exact (mem_borOf_iff hZ).2 ⟨hyL, hcr _ (hθZ a) hg1 _ h1⟩

theorem case_of_lin3 (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (hV : CFSG.Open.IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L)) {n : ℕ} (hn : 2 ≤ n)
    (hdata : E68Lin3Data (sylowBar T V L) n) (hBX : borOf T V L ≤ M)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n) :
    E68Case1 hV T M U L := by
  have hZ := center_le_sylow h hU hL hZ2
  have hLM : ¬ L ≤ M := not_le_of_component h hU.1 hL
  have hPg2 : IsPGroup 2 (pgOf T V L) := h.isPGroup_Q.to_le inf_le_left
  have hsolvB := isSolvable_borOf hZ hPg2 hdata.quot_comm
  have hCV := centralizer_le_borOf_of_root hInn hmod h hU hL hZ2 hdata.centralizer_root
  obtain ⟨-, hres, -⟩ := sandwich h hU hL
  have hPX : pgOf T V L ≤ L ⊓ M :=
    le_inf pgOf_le_left (inf_le_left.trans (inf_le_right.trans h.centralizer_le))
  have hXB : L ⊓ M ≤ borOf T V L :=
    inf_le_borOf_of_residual hZ hPX (fun hh => hLM (hh ▸ inf_le_right)) hBX hsolvB
      (hres.trans hCV) hdata.not_solvable
  exact case1_of_borel hInn hmod hV h hU hL hZ2 hBX hXB hn hdata.quot_comm hdata.card_root
    hdata.singer (Or.inr (Or.inr (Or.inl ⟨by omega, hmodel⟩)))

end Lin3

end E68Proof

end E6

end CFSG.Quasithin
