module

public import CFSG.Timmesfeld.Bridge.RootSetsConn2
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.OddTranspDefs

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

section SolvableRadical

variable {H : Type*} [Group H]

theorem solvableRadical_normal' : (CFSG.solvableRadical H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

instance solvableRadical_normal_inst' : (CFSG.solvableRadical H).Normal := solvableRadical_normal'

theorem le_solvableRadical' {N : Subgroup H} (hN : N.Normal) (hs : Group.IsSolvable N) :
    N ≤ CFSG.solvableRadical H :=
  le_sSup ⟨hN, hs⟩

theorem isSolvable_sup_of_normal' (N₁ N₂ : Subgroup H) [hN₁ : N₁.Normal] [N₂.Normal]
    [Group.IsSolvable N₁] [Group.IsSolvable N₂] :
    Group.IsSolvable (N₁ ⊔ N₂ : Subgroup H) := by
  let L : Subgroup H := N₁ ⊔ N₂
  let M : Subgroup L := N₁.subgroupOf L
  have hM : M.Normal := Subgroup.normal_subgroupOf
  have hMsolv : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : N₁ ≤ L)).toMonoidHom) (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let f : N₂ →* L ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : N₂ ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := N₁) (t := N₂)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hN₁.conj_mem' a ha b
  have : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient M

theorem isSolvable_solvableRadical' [Finite H] : Group.IsSolvable (CFSG.solvableRadical H) := by
  classical
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup H => N.Normal ∧ Group.IsSolvable N) (a := ⊥)
    ⟨inferInstance, inferInstance⟩
  have hge : ∀ N : Subgroup H, N.Normal ∧ Group.IsSolvable N → N ≤ M := by
    rintro N ⟨hN, hNs⟩
    have : M.Normal := hM.1.1
    have : Group.IsSolvable M := hM.1.2
    have h := hM.eq_of_le ⟨inferInstance, isSolvable_sup_of_normal' M N⟩ le_sup_left
    rw [h]
    exact le_sup_right
  have heq : CFSG.solvableRadical H = M := le_antisymm (sSup_le hge) (le_sSup hM.1)
  rw [heq]
  exact hM.1.2

theorem eq_bot_of_normal_isSolvable_quotient [Finite H] {N : Subgroup (H ⧸ CFSG.solvableRadical H)}
    (hN : N.Normal) (hs : Group.IsSolvable N) : N = ⊥ := by
  set R := CFSG.solvableRadical H with hR
  have : R.Normal := solvableRadical_normal'
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical'
  set ρ := QuotientGroup.mk' R with hρ
  have hle : ρ.ker ≤ N.comap ρ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hker : Group.IsSolvable ρ.ker := by
    rw [hρ, QuotientGroup.ker_mk']
    exact hRs
  have hK : Group.IsSolvable (N.comap ρ) := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) (ρ.subgroupComap N)
      fun x hx => ?_
    have hx1 : ρ (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, MonoidHom.mem_ker.mpr hx1⟩, rfl⟩
  have hKR : N.comap ρ ≤ R := le_solvableRadical' (Subgroup.Normal.comap hN ρ) hK
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
  have hx : x ∈ R := hKR hy
  exact (QuotientGroup.eq_one_iff x).2 hx

end SolvableRadical

namespace Asc72.Setup

variable {G : Type*} [Group G] {D : Set G} (hS : Setup G D)
include hS

theorem mul_not_mem_of_commutator_ne_top (hne : commutator G ≠ ⊤) {u v : G} (hu : u ∈ D)
    (hv : v ∈ D) : u * v ∉ D := by
  intro huv
  have hdisj : ∀ x ∈ D, x ∉ commutator G := by
    rcases hS.subset_or_disjoint (commutator G) with h | h
    · exact absurd (hS.eq_top_of_subset _ h) hne
    · exact h
  apply hdisj _ huv
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, hS.abelianization_eq hv hu,
    ← map_mul, hS.oddT.mul_self_eq_one hu, map_one]

end Asc72.Setup

theorem commutator_ne_top_of_mulEquiv_wreath {Y : Type*} [Group Y] {f n : ℕ} (hn : 2 ≤ n)
    (e : Y ≃* Asc72.L2Wreath f n) : commutator Y ≠ ⊤ := by
  set χ : Y →* ℤˣ :=
    (Equiv.Perm.sign.comp SemidirectProduct.rightHom).comp e.toMonoidHom with hχ
  intro htop
  have hle := Abelianization.commutator_subset_ker χ
  rw [htop] at hle
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hmem : e.symm (SemidirectProduct.inr (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)) ∈ χ.ker :=
    hle (Subgroup.mem_top _)
  rw [MonoidHom.mem_ker, hχ] at hmem
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    SemidirectProduct.rightHom_inr, Equiv.Perm.sign_swap h01] at hmem
  exact absurd hmem (by decide)

namespace Asc72

variable {G : Type*} [Group G] {D : Set G}

theorem isBenderGroup_of_conclusion [Finite G] (hS : Setup G D) {u v : G} (hu : u ∈ D)
    (hv : v ∈ D) (huv : Commute u v) (huvD : u * v ∈ D) (hC : Conclusion G D) :
    CFSG.BenderSuzuki.IsBenderGroup G := by
  rcases hC with hB | ⟨f, n, -, hn, ⟨e⟩⟩ | hAS
  · exact hB
  · exact absurd huvD (hS.mul_not_mem_of_commutator_ne_top
      (commutator_ne_top_of_mulEquiv_wreath (by omega) e) hu hv)
  · exfalso
    obtain ⟨M, hMn, -, -, -, -, hidx, hwidth, -⟩ := hAS
    have hDM : ∀ w ∈ D, w ∉ M := by
      rcases hS.subset_or_disjoint M with h' | h'
      · exfalso
        have := hS.eq_top_of_subset M h'
        rw [this, Subgroup.index_top] at hidx
        omega
      · exact h'
    set ρ := QuotientGroup.mk' M
    have hne1 : ∀ w ∈ D, ρ w ≠ 1 := fun w hw h1 => hDM w hw ((QuotientGroup.eq_one_iff w).1 h1)
    have hu2 : ρ u * ρ u = 1 := by rw [← map_mul, hS.oddT.mul_self_eq_one hu, map_one]
    have hv2 : ρ v * ρ v = 1 := by rw [← map_mul, hS.oddT.mul_self_eq_one hv, map_one]
    have hP2 : IsPGroup 2 (Subgroup.closure ({ρ u, ρ v} : Set (G ⧸ M))) := by
      refine isPGroup_closure_of_pairwise ?_ ?_
      · rintro s (rfl | rfl) t (rfl | rfl) -
        · exact Commute.refl _
        · exact huv.map ρ
        · exact (huv.map ρ).symm
        · exact Commute.refl _
      · rintro s (rfl | rfl)
        · exact hu2
        · exact hv2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S, hS2⟩ := hP2.exists_le_sylow
    have hmemS : ∀ t ∈ ({ρ u, ρ v} : Set (G ⧸ M)), t ∈ (S : Subgroup (G ⧸ M)) :=
      fun t ht => hS2 (Subgroup.subset_closure ht)
    obtain ⟨α, hα⟩ := Set.ncard_eq_one.1 (hwidth S)
    have huS : ρ u ∈ ρ '' D ∩ (S : Set (G ⧸ M)) := ⟨⟨u, hu, rfl⟩, hmemS _ (by simp)⟩
    have huvS' : ρ (u * v) ∈ (S : Subgroup (G ⧸ M)) := by
      rw [map_mul]
      exact S.mul_mem (hmemS _ (by simp)) (hmemS _ (by simp))
    have huvS : ρ (u * v) ∈ ρ '' D ∩ (S : Set (G ⧸ M)) := ⟨⟨u * v, huvD, rfl⟩, huvS'⟩
    rw [hα] at huS huvS
    have h1 : ρ u = ρ (u * v) := huS.trans huvS.symm
    rw [map_mul] at h1
    apply hne1 v hv
    have := congrArg ((ρ u)⁻¹ * ·) h1
    simpa using this.symm

end Asc72

theorem closure_preimage_subtype_eq_top {G : Type*} [Group G] {N : Subgroup G} {S : Set G}
    (hSN : S ⊆ N) (hgen : Subgroup.closure S = N) : Subgroup.closure (N.subtype ⁻¹' S) = ⊤ := by
  apply Subgroup.map_injective N.subtype_injective
  rw [MonoidHom.map_closure, Set.image_preimage_eq_inter_range, Subgroup.coe_subtype,
    Subtype.range_coe, Set.inter_eq_left.2 hSN, hgen, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem reach_of_reach_subtype {G : Type*} [Group G] {D : Set G} {K : Subgroup G} {S : Set K}
    (hS : ∀ w ∈ S, (w : G) ∈ D) {u v : K} (h : Reach S u v) : Reach D (u : G) (v : G) := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih =>
    exact reach_trans ih (reach_of_commute (hS _ hbc.1) (hS _ hbc.2.1) (hbc.2.2.map K.subtype))

namespace Step6

variable {G : Type} [Group G] {D : Set G} {a b c x z : G} {P : Subgroup G}

@[expose] def lclass (D : Set G) (x : G) (P : Subgroup G) : Set (lsub D x P) :=
  {w | (w : G) ∈ classIn (lsub D x P) x}

theorem setup (hC : ConnCex D) (h : Step6 D a b c x z P) :
    Asc72.Setup (lsub D x P) (lclass D x P) := by
  refine ⟨⟨⟨x, mem_lsub_x⟩, ?_⟩, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨g, hg, hw⟩
      exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simp [hw])⟩
    · intro hw
      obtain ⟨g, hg⟩ := isConj_iff.1 hw
      refine ⟨g, g.2, ?_⟩
      rw [← hg]
      simp
  · exact (h.isOddTransp_classIn hC).preimage _
  · exact closure_preimage_subtype_eq_top (classIn_subset _ mem_lsub_x) (h.closure_classIn hC)

theorem mem_lclass (hC : ConnCex D) (h : Step6 D a b c x z P) {u : G} (hu : u ∈ D)
    (huP : u ∈ P) : (⟨u, mem_lsub_of_mem hu huP⟩ : lsub D x P) ∈ lclass D x P :=
  h.mem_classIn hC hu huP

theorem not_isSolvable (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ¬ Group.IsSolvable (lsub D x P) := by
  have := hC.setting.finite
  intro hsol
  obtain ⟨e, he, f, hf, heP, hfP, -, hefD⟩ := h.hLL
  have hS := h.setup hC
  exact hS.mul_not_mem_of_isSolvable hsol (h.mem_lclass hC he heP) (h.mem_lclass hC hf hfP)
    (h.mem_lclass hC hefD (P.mul_mem heP hfP))

theorem not_mem_solvableRadical (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∀ w ∈ lclass D x P, w ∉ CFSG.solvableRadical (lsub D x P) := by
  have := hC.setting.finite
  have hS := h.setup hC
  rcases hS.subset_or_disjoint (CFSG.solvableRadical (lsub D x P)) with h' | h'
  · exfalso
    apply h.not_isSolvable hC
    have htop := hS.eq_top_of_subset _ h'
    have hRs : Group.IsSolvable (CFSG.solvableRadical (lsub D x P)) :=
      isSolvable_solvableRadical'
    rw [htop] at hRs
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (lsub D x P)).subtype)
      (fun g => ⟨⟨g, trivial⟩, rfl⟩)
  · exact h'

theorem quotient_setup (hC : ConnCex D) (h : Step6 D a b c x z P) :
    Asc72.Setup (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P))
      (QuotientGroup.mk' (CFSG.solvableRadical (lsub D x P)) '' lclass D x P) :=
  (h.setup hC).map _ (QuotientGroup.mk'_surjective _) fun d hd h1 =>
    h.not_mem_solvableRadical hC d hd ((QuotientGroup.eq_one_iff d).1 h1)

theorem quotient_disconnected (hC : ConnCex D) (h : Step6 D a b c x z P) :
    Disconnected (QuotientGroup.mk' (CFSG.solvableRadical (lsub D x P)) '' lclass D x P) := by
  have := hC.setting.finite
  set X := lsub D x P with hX
  set R := CFSG.solvableRadical X with hR
  have hS := h.setup hC
  have hns := h.not_isSolvable hC
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical'
  refine ⟨QuotientGroup.mk' R ⟨a, mem_lsub_of_mem h.ha h.haP⟩,
    ⟨_, h.mem_lclass hC h.ha h.haP, rfl⟩, QuotientGroup.mk' R ⟨x, mem_lsub_x⟩,
    ⟨_, mem_classIn_self _ x, rfl⟩, fun hr => ?_⟩
  have hlift : ∀ u ∈ lclass D x P, ∀ v ∈ lclass D x P, u⁻¹ * v ∈ R →
      Reach (lclass D x P) u v := fun u hu v hv huv =>
    Asc72.reach_of_inv_mul_mem_solvable hS hns hRs hu hv huv
  have hrE := Asc72.reach_of_reach_quotient hS.oddT hlift (h.mem_lclass hC h.ha h.haP)
    (mem_classIn_self _ x) hr
  exact h.hax (reach_of_reach_subtype
    (fun w hw => classIn_subset_of_normal hC.setting.normal _ h.hx hw) hrE)

theorem exists_mul_mem_image (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∃ u ∈ QuotientGroup.mk' (CFSG.solvableRadical (lsub D x P)) '' lclass D x P,
      ∃ v ∈ QuotientGroup.mk' (CFSG.solvableRadical (lsub D x P)) '' lclass D x P,
        Commute u v ∧ u * v ∈ QuotientGroup.mk' (CFSG.solvableRadical (lsub D x P)) ''
          lclass D x P := by
  obtain ⟨e, he, f, hf, heP, hfP, -, hefD⟩ := h.hLL
  set π := QuotientGroup.mk' (CFSG.solvableRadical (lsub D x P))
  have hcomm : Commute (⟨e, mem_lsub_of_mem he heP⟩ : lsub D x P) ⟨f, mem_lsub_of_mem hf hfP⟩ :=
    Subtype.ext (h.commute_of_mem hC he hf heP hfP).eq
  refine ⟨π ⟨e, _⟩, ⟨_, h.mem_lclass hC he heP, rfl⟩, π ⟨f, _⟩, ⟨_, h.mem_lclass hC hf hfP, rfl⟩,
    hcomm.map π, ⟨_, h.mem_lclass hC hefD (P.mul_mem heP hfP), ?_⟩⟩
  rw [← map_mul]
  rfl

theorem isBenderGroup (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    CFSG.BenderSuzuki.IsBenderGroup (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P)) := by
  have := hC.setting.finite
  have hS' := h.quotient_setup hC
  obtain ⟨u, hu, v, hv, huv, huvD⟩ := h.exists_mul_mem_image hC
  have hne : u ≠ v := by
    rintro rfl
    exact hS'.oddT.ne_one huvD (hS'.oddT.mul_self_eq_one hu)
  exact hB _ _ hS' (fun N hN hs => eq_bot_of_normal_isSolvable_quotient hN hs)
    ⟨u, hu, v, hv, hne, huv, huvD⟩ (h.quotient_disconnected hC)

end Step6

end CFSG.Timmesfeld.Bridge
