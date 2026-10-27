module

public import CFSG.Quasithin.Background.ONanE68Act
public import CFSG.Quasithin.Background.GoldschmidtTDE68Bar
public import CFSG.Quasithin.Background.ONanE68LieFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68

section Basic

variable {G : Type} [Group G] {L : Subgroup G}

abbrev piBar (L : Subgroup G) : ↥L →* Bar.Qbar L :=
  QuotientGroup.mk' (Subgroup.center ↥L)

theorem piBar_surjective : Function.Surjective (piBar L) := QuotientGroup.mk'_surjective _

theorem ker_piBar : (piBar L).ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _

theorem center_qbar_eq_bot (hq : CFSG.IsQuasisimple ↥L) : Subgroup.center (Bar.Qbar L) = ⊥ := by
  rcases hq.2.1.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar.Qbar L)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem pre_img_eq {Y : Subgroup G} (hYL : Y ≤ L) (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Y) :
    Fin257.pre (piBar L) ((Y.subgroupOf L).map (piBar L)) = Y := by
  ext x
  rw [Fin257.mem_pre]
  constructor
  · rintro ⟨hxL, y, hy, hyx⟩
    have h1 : y⁻¹ * (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← ker_piBar, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have h2 : (((y⁻¹ * ⟨x, hxL⟩ : ↥L)) : G) ∈ Y := hZ _ h1
    have h3 : ((y : ↥L) : G) ∈ Y := hy
    have h4 := Y.mul_mem h3 h2
    simpa using h4
  · intro hx
    exact ⟨hYL hx, ⟨x, hYL hx⟩, hx, rfl⟩

theorem isSylowTwoOf_subgroupOf_top_of {P K : Subgroup G} (hP : IsSylowTwoOf P K) :
    IsSylowTwoOf (P.subgroupOf K) ⊤ := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  have h : ((P.subgroupOf K).subgroupOf (⊤ : Subgroup K)).index = (P.subgroupOf K).index :=
    Subgroup.relIndex_top_right (P.subgroupOf K)
  rw [h]
  exact hP.2.2

end Basic

section Sylow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def sylowBar (T V L : Subgroup G) : Subgroup (Bar.Qbar L) :=
  (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L).subgroupOf L).map (piBar L)

omit [Finite G] in
theorem isSylowTwoOf_map_piBar {P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hZ : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ P) :
    IsSylowTwoOf ((P.subgroupOf L).map (piBar L)) ⊤ := by
  have hP0 := isSylowTwoOf_subgroupOf_top_of hP
  have hker : (piBar L).ker ≤ P.subgroupOf L := by
    rw [ker_piBar]
    intro z hz
    exact hZ z hz
  refine ⟨le_top, hP0.2.1.map _, ?_⟩
  have h1 : ((P.subgroupOf L).map (piBar L)).comap (piBar L) = P.subgroupOf L :=
    Subgroup.comap_map_eq_self hker
  have h2 := Subgroup.index_comap_of_surjective ((P.subgroupOf L).map (piBar L))
    (piBar_surjective (L := L))
  rw [h1] at h2
  have h3 := hP0.2.2
  rw [show ((P.subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index = (P.subgroupOf L).index from
    Subgroup.relIndex_top_right _] at h3
  rw [show (((P.subgroupOf L).map (piBar L)).subgroupOf ⊤).index =
    ((P.subgroupOf L).map (piBar L)).index from Subgroup.relIndex_top_right _, ← h2]
  exact h3

end Sylow

section Theta

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem center_le_sylow (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hZ : IsPGroup 2 (Subgroup.center ↥L)) :
    ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ (T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L := by
  intro z hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (e6_5_one h hU) hL.1 hL.2.2
  have hzp : z ∈ CFSG.Open.pCore 2 ↥L :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hZ hz
  have h1 : (z : G) ∈ pCoreOf 2 L := ⟨z, hzp, rfl⟩
  exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS h1

theorem sylowInB_coe_eq (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    ((sylowInB (baseHyp h hU hL) : Sylow 2 ↥L) : Subgroup ↥L) =
      ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L).subgroupOf L := by
  have e : ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ Subgroup.normalizer (L : Set G)) ⊓ L =
      (T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L := by
    rw [inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : L ≤ _)]
  unfold sylowInB
  rw [A4.toSylow_coe, e]

theorem exists_theta (hInn : Ch1.EvenLieAutInner) (hmod : Ch1.SQTKCharTwoLie (Bar.Qbar L))
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) :
    ∃ θ : ↥V →* Bar.Qbar L,
      (∀ a : ↥V, Bar.barHom L ⟨a, le_normalizer_of_component h hU hL a.2⟩ =
        MulAut.conj (θ a)) ∧ ∀ a : ↥V, θ a ∈ omegaCenter (sylowBar T V L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbase := baseHyp h hU hL
  have hq : CFSG.IsQuasisimple ↥L := hbase.quasisimple
  have hZ0 := center_qbar_eq_bot hq
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := leN_base hbase
  have hVN' : ∀ a : ↥V, (a : G) ∈ Subgroup.normalizer (L : Set G) := fun a => hVN a.2
  let PS : Sylow 2 (Bar.Qbar L) := (sylowInB hbase).mapSurjective piBar_surjective
  have hPS : (PS : Subgroup (Bar.Qbar L)) = sylowBar T V L := by
    change ((sylowInB hbase : Sylow 2 ↥L) : Subgroup ↥L).map (piBar L) = _
    rw [sylowInB_coe_eq h hU hL]
    rfl
  have hinner : ∀ a : ↥V, ∃ g : Bar.Qbar L,
      Bar.barHom L ⟨a, hVN' a⟩ = MulAut.conj g ∧ g ∈ omegaCenter (sylowBar T V L) := by
    intro a
    set β : MulAut (Bar.Qbar L) := Bar.barHom L ⟨a, hVN' a⟩ with hβ
    have haa : (⟨a, hVN' a⟩ : ↥(Subgroup.normalizer (L : Set G))) *
        ⟨a, hVN' a⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using hbase.elemAbelian.2 a a.2)
    have hββ : β * β = 1 := by
      rw [hβ, ← map_mul, haa, map_one]
    have hinv : ∀ x, β (β x) = x := fun x => by
      have := congrArg (fun φ : MulAut (Bar.Qbar L) => φ x) hββ
      simpa using this
    have hfixP : ∀ t ∈ (PS : Subgroup (Bar.Qbar L)), β t = t := by
      intro t ht
      change t ∈ ((sylowInB hbase : Sylow 2 ↥L) : Subgroup ↥L).map (piBar L) at ht
      obtain ⟨x, hx, rfl⟩ := ht
      have hxR : (x : G) ∈ (T ⊓ Subgroup.centralizer (V : Set G)) ⊓
          Subgroup.normalizer (L : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
      have hcomm : (a : G) * x = x * a :=
        Subgroup.mem_centralizer_iff.1 (hbase.centralizer hxR) a a.2
      exact CFSG.Quasithin.E6.Bar.barHom_mk_of_comm (L := L) ⟨(a : G), hVN' a⟩ x hcomm
    obtain ⟨l, hl⟩ := hInn (Bar.Qbar L) hmod β hinv ⟨PS, hfixP⟩
    have hβc : β = MulAut.conj l⁻¹ := MulEquiv.ext fun x => by
      rw [hl x, MulAut.conj_apply]
      simp
    refine ⟨l⁻¹, hβc, ?_⟩
    have hgg : l⁻¹ * l⁻¹ = 1 := by
      have h1 : MulAut.conj (l⁻¹ * l⁻¹) = 1 := by rw [map_mul, ← hβc, hββ]
      have h2 : l⁻¹ * l⁻¹ ∈ Subgroup.center (Bar.Qbar L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h3 := congrArg (fun φ : MulAut (Bar.Qbar L) => φ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc y * (l⁻¹ * l⁻¹) = (l⁻¹ * l⁻¹ * y * (l⁻¹ * l⁻¹)⁻¹) * (l⁻¹ * l⁻¹) := by rw [h3]
          _ = l⁻¹ * l⁻¹ * y := by group
      rw [hZ0, Subgroup.mem_bot] at h2
      exact h2
    have hcommP : ∀ t ∈ (PS : Subgroup (Bar.Qbar L)), l⁻¹ * t = t * l⁻¹ := by
      intro t ht
      have h1 := hfixP t ht
      rw [hβc, MulAut.conj_apply] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have hmem := mem_omegaZ_of_commute PS hcommP hgg
    rw [← hPS]
    exact hmem
  choose g hg using hinner
  have hg_mul : ∀ a b : ↥V, g (a * b) = g a * g b := by
    intro a b
    apply conj_injective_of_center hZ0
    rw [map_mul, ← (hg a).1, ← (hg b).1, ← (hg (a * b)).1]
    have e : (⟨((a * b : ↥V) : G), hVN' (a * b)⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨(a : G), hVN' a⟩ * ⟨(b : G), hVN' b⟩ := Subtype.ext rfl
    rw [e, map_mul]
  exact ⟨MonoidHom.mk' g hg_mul, fun a => (hg a).1, fun a => (hg a).2⟩

end Theta

section ThetaProps

variable {G : Type} [Group G] {V L : Subgroup G} (hVN : V ≤ Subgroup.normalizer (L : Set G))
  (θ : ↥V →* Bar.Qbar L)
  (hθ : ∀ a : ↥V, Bar.barHom L ⟨a, hVN a.2⟩ = MulAut.conj (θ a))

include hθ

theorem theta_apply (a : ↥V) (x y : ↥L) (h : (y : G) = (a : G) * x * (a : G)⁻¹) :
    piBar L y = θ a * piBar L x * (θ a)⁻¹ := by
  have := CFSG.Quasithin.E6.Bar.barHom_mk (L := L) ⟨(a : G), hVN a.2⟩ x y h
  rw [hθ a, MulAut.conj_apply] at this
  exact this.symm

theorem theta_eq_one_iff (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L)
    (a : ↥V) : θ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  have h1 : θ a = 1 ↔ MulAut.conj (θ a) = 1 := by
    constructor
    · intro h; rw [h, map_one]
    · intro h
      exact conj_injective_of_center hZ0 (h.trans (map_one _).symm)
  rw [h1, ← hθ a, CFSG.Quasithin.E6.Bar.barHom_eq_one_iff hperf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact (h ⟨x, hx⟩).symm
  · intro h x
    exact (h x x.2).symm

theorem theta_equivariant (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (x : ↥L) (a b : ↥V)
    (hb : (b : G) = (x : G) * a * (x : G)⁻¹) :
    θ b = piBar L x * θ a * (piBar L x)⁻¹ := by
  apply conj_injective_of_center hZ0
  rw [map_mul, map_mul, map_inv, ← hθ a, ← hθ b]
  have e : (⟨(b : G), hVN b.2⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨(x : G), Subgroup.le_normalizer x.2⟩ * ⟨(a : G), hVN a.2⟩ *
        ⟨(x : G), Subgroup.le_normalizer x.2⟩⁻¹ := Subtype.ext (by rw [hb]; rfl)
  rw [e, map_mul, map_mul, map_inv, CFSG.Quasithin.E6.Bar.barHom_of_mem x]
  rfl

theorem theta_comm_of_comm (l : ↥L) (a : ↥V) (h : (l : G) * a = a * l) :
    piBar L l * θ a = θ a * piBar L l := by
  have h1 := CFSG.Quasithin.E6.Bar.barHom_mk_of_comm (L := L) ⟨(a : G), hVN a.2⟩ l h.symm
  rw [hθ a, MulAut.conj_apply] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem comm_of_theta_comm (hinj : Function.Injective (piBar L)) (l : ↥L) (a : ↥V)
    (h : piBar L l * θ a = θ a * piBar L l) : (l : G) * a = a * l := by
  have h1 : θ a * piBar L l * (θ a)⁻¹ = piBar L l := by
    rw [← h]
    group
  have h2 := theta_apply hVN θ hθ a l ⟨(a : G) * l * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.1
    (hVN a.2) l).1 l.2⟩ rfl
  rw [h1] at h2
  have h3 := hinj h2
  have h4 : (a : G) * l * (a : G)⁻¹ = l := congrArg Subtype.val h3
  calc (l : G) * a = ((a : G) * l * (a : G)⁻¹) * a := by rw [h4]
    _ = a * l := by group

theorem ker_theta (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L) :
    θ.ker = (V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf V := by
  ext a
  rw [MonoidHom.mem_ker, theta_eq_one_iff hVN θ hθ hZ0 hperf, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

theorem card_range_theta (hZ0 : Subgroup.center (Bar.Qbar L) = ⊥) (hperf : Group.IsPerfect ↥L) :
    Nat.card θ.range = (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := by
  rw [← Subgroup.index_ker, ker_theta hVN θ hθ hZ0 hperf]
  rfl

omit hθ

end ThetaProps

end E68Proof

end E6

end CFSG.Quasithin
