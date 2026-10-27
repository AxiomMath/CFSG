module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Ind
public import CFSG.Quasithin.Background.GoldschmidtTDE68Qs

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar

variable {Y : Type} [Group Y] {L R K : Subgroup Y} {u : Y} {G : Type} [Group G] {D : Subgroup G}

structure CentSetup (e : Qbar L ≃* G) (R : Subgroup Y) (D : Subgroup G) (u : Y) : Prop where
  perfect : Group.IsPerfect ↥L
  imgBar_eq : (imgBar L R).map e.toMonoidHom = D
  le_normalizer : R ≤ Subgroup.normalizer (L : Set Y)
  mem : u ∈ R
  central : ∀ r ∈ R, u * r = r * u
  sq : u ^ 2 = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)

variable {e : Qbar L ≃* G}

@[expose] def CentSetup.bu (h : CentSetup e R D u) : ↥(Subgroup.normalizer (L : Set Y)) :=
  ⟨u, h.le_normalizer h.mem⟩

theorem CentSetup.indHom_mem (h : CentSetup e R D u) : indHom L e h.bu ∈ InvSet D := by
  refine ⟨?_, ?_, fun d hd => indHom_commute e h.imgBar_eq h.bu h.central d hd⟩
  · intro h1
    refine h.not_mem (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    exact ((indHom_eq_one_iff e h.perfect h.bu).1 h1 ⟨x, hx⟩).symm
  · rw [← map_mul]
    have : h.bu * h.bu = 1 := Subtype.ext (by
      show u * u = 1
      simpa [pow_two] using h.sq)
    rw [this, map_one]

abbrev centL (L : Subgroup Y) (u : Y) : Subgroup Y := L ⊓ Subgroup.centralizer ({u} : Set Y)

@[expose] noncomputable def compHom (e : Qbar L ≃* G) (u : Y) (K : Subgroup Y) :
    ↥(K.subgroupOf (centL L u)) →* G :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥L)).comp
    ((Subgroup.inclusion (show centL L u ≤ L from inf_le_left)).comp
      (K.subgroupOf (centL L u)).subtype))

theorem compHom_apply (k : ↥(K.subgroupOf (centL L u))) :
    compHom e u K k = e (QuotientGroup.mk ⟨((k : ↥(centL L u)) : Y), (k : ↥(centL L u)).2.1⟩) :=
  rfl

theorem ker_compHom_le_center :
    (compHom e u K).ker ≤ Subgroup.center ↥(K.subgroupOf (centL L u)) := by
  intro k hk
  rw [MonoidHom.mem_ker, compHom_apply] at hk
  have h1 : (QuotientGroup.mk ⟨((k : ↥(centL L u)) : Y), (k : ↥(centL L u)).2.1⟩ : Qbar L) = 1 :=
    e.injective (by rw [hk, map_one])
  have hx := (QuotientGroup.eq_one_iff _).1 h1
  rw [Subgroup.mem_center_iff]
  intro k'
  apply Subtype.ext
  apply Subtype.ext
  have := Subgroup.mem_center_iff.1 hx ⟨((k' : ↥(centL L u)) : Y), (k' : ↥(centL L u)).2.1⟩
  have h2 : ((k' : ↥(centL L u)) : Y) * ((k : ↥(centL L u)) : Y) =
      ((k : ↥(centL L u)) : Y) * ((k' : ↥(centL L u)) : Y) := congrArg Subtype.val this
  exact h2

theorem compHom_fixed (h : CentSetup e R D u) (k : ↥(K.subgroupOf (centL L u))) :
    indHom L e h.bu (compHom e u K k) = compHom e u K k := by
  rw [compHom_apply, indHom_apply]
  congr 1
  refine barHom_mk_of_comm h.bu _ ?_
  have := Subgroup.mem_centralizer_singleton_iff.1 (k : ↥(centL L u)).2.2
  exact this.symm

theorem range_compHom_le (h : CentSetup e R D u) :
    (compHom e u K).range ≤ fixedSub (indHom L e h.bu) := by
  rintro _ ⟨k, rfl⟩
  exact compHom_fixed h k

theorem card_ker_compHom_dvd :
    Nat.card (compHom e u K).ker ∣ Nat.card ↥(Subgroup.center ↥L) := by
  let ι : ↥(K.subgroupOf (centL L u)) →* ↥L :=
    (Subgroup.inclusion (show centL L u ≤ L from inf_le_left)).comp
      (K.subgroupOf (centL L u)).subtype
  have hι : Function.Injective ι := fun a b hab => by
    have h1 : ((a : ↥(centL L u)) : Y) = ((b : ↥(centL L u)) : Y) :=
      congrArg (fun x : ↥L => (x : Y)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hmem : ∀ k : ↥(compHom e u K).ker, ι k ∈ Subgroup.center ↥L := by
    intro k
    have hk := k.2
    rw [MonoidHom.mem_ker, compHom_apply] at hk
    have h1 : (QuotientGroup.mk ⟨((k.1 : ↥(centL L u)) : Y), (k.1 : ↥(centL L u)).2.1⟩ :
        Qbar L) = 1 := e.injective (by rw [hk, map_one])
    exact (QuotientGroup.eq_one_iff _).1 h1
  let f : ↥(compHom e u K).ker →* ↥(Subgroup.center ↥L) :=
    (ι.comp (compHom e u K).ker.subtype).codRestrict _ hmem
  refine Subgroup.card_dvd_of_injective f fun a b hab => ?_
  have : ι a = ι b := congrArg Subtype.val hab
  exact Subtype.ext (hι this)

theorem false_of_solvable (h : CentSetup e R D u)
    (hs : Group.IsSolvable ↥(fixedSub (indHom L e h.bu)))
    (hq : CFSG.IsQuasisimple ↥(K.subgroupOf (centL L u))) [Finite Y] : False := by
  refine Qs.false_of_hom_solvable hq (compHom e u K) ker_compHom_le_center ?_
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (range_compHom_le h))
    (Subgroup.inclusion_injective (range_compHom_le h))

theorem card_comp_eq_sixty [Finite Y] (h : CentSetup e R D u)
    (hZ : Nat.card ↥(Subgroup.center ↥L) ∣ 3) (N : Subgroup G) (hN : Nat.card N = 60)
    (hNle : ∀ H : Subgroup G, H ≤ fixedSub (indHom L e h.bu) → Group.IsPerfect ↥H → H ≤ N)
    (hKC : K ≤ centL L u) (hq : CFSG.IsQuasisimple ↥(K.subgroupOf (centL L u))) :
    Nat.card ↥K = 60 := by
  have hK0 : Nat.card ↥(K.subgroupOf (centL L u)) = 60 := by
    refine Qs.card_eq_sixty_of_hom hq (compHom e u K) ker_compHom_le_center
      (card_ker_compHom_dvd.trans hZ) N hN ?_
    have := hq.1
    exact hNle _ (range_compHom_le h) (Group.IsPerfect.range _)
  rw [← hK0]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv).symm

end CFSG.Quasithin.E6.Alt
