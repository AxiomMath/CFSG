module

public import CFSG.Quasithin.Vol2.Ch8Sec2InspHolds
public import CFSG.Quasithin.Vol2.Ch8Sec2Step13
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.ModO2Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.GroupTheory.SteinbergCBFTHall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.G3
open scoped IsMulCommutative

@[expose] def Stmt8_2_11_modules : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
    ¬ Row711M24Code T L I → ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ch8Lz L z ∈ cComp (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      T ≤ Subgroup.normalizer (ch8Lz L z : Set G) ∧
      (∀ n : ℕ, Row711L3Nine T L I n → n = 1) ∧
      (Row711L3Nine T L I 1 →
        ∃ (α : ↥(ch8Lz L z) →* alternatingGroup (Fin 5))
          (β : ↥(fsuV T I) →* Multiplicative (evenWeight 5)),
          Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥(ch8Lz L z) ∧
          Function.Surjective β ∧ β.ker = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I) ∧
          ∀ (x : ↥(ch8Lz L z)) (v w : ↥(fsuV T I)), (x : G) * (v : G) * (x : G)⁻¹ = (w : G) →
            ∀ i : Fin 5, ((Multiplicative.toAdd (β w) : evenWeight 5) : Fin 5 → ZMod 2) i =
              ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2)
                (((α x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i)) ∧
      (Row711M22Code T L I →
        Nat.card (↥(ch8Lz L z) ⧸ CFSG.pCore 2 ↥(ch8Lz L z)) = 360 ∧
        ∃ θ : ↥(fsuV T I) →* Multiplicative (Fin 5 → ZMod 2),
          Function.Surjective θ ∧ θ.ker = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I)) ∧
      (Row711M24Cocode T L I →
        Nat.card (↥(ch8Lz L z) ⧸ CFSG.pCore 2 ↥(ch8Lz L z)) = 1080 ∧
        ∃ θ : ↥(fsuV T I) →* Multiplicative (Fin 4 → ZMod 2),
          Function.Surjective θ ∧ θ.ker = (ch8Vz (fsuV T I) L z).subgroupOf (fsuV T I))

section Generic

variable {G : Type} [Group G]

theorem mem_pCore_iff_mem_pCoreOf_sub {H : Subgroup G} (x : ↥H) :
    x ∈ CFSG.pCore 2 ↥H ↔ (x : G) ∈ pCoreOf 2 H := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem pCoreOf_le_self (H : Subgroup G) : pCoreOf 2 H ≤ H := by
  rintro y ⟨z, -, rfl⟩
  exact z.2

theorem exists_comp_eq_of_surj_ker_le {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (hf : Function.Surjective f) (g : X →* Z) (hk : f.ker ≤ g.ker) :
    ∃ h : Y →* Z, h.comp f = g := by
  refine ⟨(QuotientGroup.lift f.ker g hk).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom, ?_⟩
  ext x
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) =
      (x : X ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  exact QuotientGroup.lift_mk' _ _ _

theorem exists_mulEquiv_comp_eq_of_surj_ker_eq {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : X →* Z) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) : ∃ e : Y ≃* Z, ∀ x : X, e (f x) = g x := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)), fun x => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) =
      (x : X ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end Generic

section Image

variable {G : Type} [Group G] [Finite G]

theorem range_modO2Image {C L : Subgroup G} (hLC : L ≤ C) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥C)).comp (Subgroup.inclusion hLC)).range =
      modO2Image C L := by
  unfold modO2Image
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

noncomputable def imgHom {C L : Subgroup G} (hLC : L ≤ C) : ↥L →* ↥(modO2Image C L) :=
  (MulEquiv.subgroupCongr (range_modO2Image hLC)).toMonoidHom.comp
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥C)).comp (Subgroup.inclusion hLC)).rangeRestrict

theorem imgHom_surjective {C L : Subgroup G} (hLC : L ≤ C) :
    Function.Surjective (imgHom hLC) :=
  (MulEquiv.subgroupCongr (range_modO2Image hLC)).surjective.comp
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥C)).comp (Subgroup.inclusion hLC)).rangeRestrict_surjective

theorem imgHom_val {C L : Subgroup G} (hLC : L ≤ C) (x : ↥L) :
    ((imgHom hLC x : ↥(modO2Image C L)) : ↥C ⧸ CFSG.pCore 2 ↥C) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥C) (Subgroup.inclusion hLC x) := by
  rfl

theorem imgHom_eq_one_iff {C L : Subgroup G} (hLC : L ≤ C) (x : ↥L) :
    imgHom hLC x = 1 ↔ (x : G) ∈ pCoreOf 2 C := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [imgHom_val, OneMemClass.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (mem_pCore_iff_mem_pCoreOf_sub _).mp h1
  · intro hx
    apply Subtype.ext
    rw [imgHom_val, OneMemClass.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_pCore_iff_mem_pCoreOf_sub _).mpr hx

theorem isPGroup_ker_imgHom {C L : Subgroup G} (hLC : L ≤ C) :
    IsPGroup 2 (imgHom hLC).ker := by
  intro g
  have hc : Subgroup.inclusion hLC g.1 ∈ CFSG.pCore 2 ↥C := by
    rw [mem_pCore_iff_mem_pCoreOf_sub]
    exact (imgHom_eq_one_iff hLC g.1).mp (MonoidHom.mem_ker.mp g.2)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)) ⟨_, hc⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : Subgroup.inclusion hLC (g.1 ^ 2 ^ k) = 1 := by
    rw [map_pow]
    have h2 := congrArg Subtype.val hk
    simpa using h2
  have h3 : g.1 ^ 2 ^ k = 1 := by
    apply Subgroup.inclusion_injective hLC
    rw [h1, map_one]
  simpa using h3

theorem pCore_map_imgHom {C L : Subgroup G} (hLC : L ≤ C) :
    (CFSG.pCore 2 ↥L).map (imgHom hLC) = CFSG.pCore 2 ↥(modO2Image C L) :=
  CFSG.GroupTheory.FT63ChII.pCore_map_of_surjective (imgHom_surjective hLC)
    (isPGroup_ker_imgHom hLC)

theorem range_imgHom_inclusion {C L V : Subgroup G} (hLC : L ≤ C) (hVL : V ≤ L)
    (hEL : pCoreOf 2 L = pCoreOf 2 C ⊔ V) :
    ((imgHom hLC).comp (Subgroup.inclusion hVL)).range =
      (CFSG.pCore 2 ↥L).map (imgHom hLC) := by
  have hC_L : pCoreOf 2 C ≤ pCoreOf 2 L := by
    rw [hEL]
    exact le_sup_left
  have hV_L : V ≤ pCoreOf 2 L := by
    rw [hEL]
    exact le_sup_right
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨Subgroup.inclusion hVL v, ?_, rfl⟩
    exact (mem_pCore_iff_mem_pCoreOf_sub _).mpr (hV_L v.2)
  · rintro _ ⟨x, hx, rfl⟩
    set R := ((imgHom hLC).comp (Subgroup.inclusion hVL)).range with hR
    have hle : pCoreOf 2 L ≤ (R.comap (imgHom hLC)).map L.subtype := by
      rw [hEL]
      refine sup_le ?_ ?_
      · intro g hg
        have hgL : g ∈ L := pCoreOf_le_self L (hC_L hg)
        refine ⟨⟨g, hgL⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, (imgHom_eq_one_iff hLC ⟨g, hgL⟩).mpr hg]
        exact R.one_mem
      · intro v hv
        refine ⟨⟨v, hVL hv⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        exact ⟨⟨v, hv⟩, rfl⟩
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (hle ((mem_pCore_iff_mem_pCoreOf_sub x).mp hx))
    have hwx' : w = x := Subtype.ext hwx
    rw [hwx'] at hw
    exact Subgroup.mem_comap.mp hw

theorem ker_imgHom_inclusion {C L V : Subgroup G} (hLC : L ≤ C) (hVL : V ≤ L) :
    ((imgHom hLC).comp (Subgroup.inclusion hVL)).ker = (pCoreOf 2 C ⊓ V).subgroupOf V := by
  ext v
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    imgHom_eq_one_iff]
  exact ⟨fun h => ⟨h, v.2⟩, fun h => h.1⟩

end Image

section Delta5

variable {G : Type} [Group G] [Finite G]

theorem exists_pCore_image_iso {C L V : Subgroup G} (hLC : L ≤ C) (hVL : V ≤ L)
    (hEL : pCoreOf 2 L = pCoreOf 2 C ⊔ V) :
    ∃ Θc : ↥V →* ↥(CFSG.pCore 2 ↥(modO2Image C L)),
      Function.Surjective Θc ∧ Θc.ker = (pCoreOf 2 C ⊓ V).subgroupOf V ∧
      ∀ v : ↥V, ((Θc v : ↥(CFSG.pCore 2 ↥(modO2Image C L))) : ↥(modO2Image C L)) =
        imgHom hLC (Subgroup.inclusion hVL v) := by
  have hrange : ((imgHom hLC).comp (Subgroup.inclusion hVL)).range =
      CFSG.pCore 2 ↥(modO2Image C L) :=
    (range_imgHom_inclusion hLC hVL hEL).trans (pCore_map_imgHom hLC)
  refine ⟨(MulEquiv.subgroupCongr hrange).toMonoidHom.comp
    ((imgHom hLC).comp (Subgroup.inclusion hVL)).rangeRestrict, ?_, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hrange).surjective.comp
      ((imgHom hLC).comp (Subgroup.inclusion hVL)).rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective _ (MulEquiv.subgroupCongr hrange).toMonoidHom
      (MulEquiv.injective _), MonoidHom.ker_rangeRestrict, ker_imgHom_inclusion hLC hVL]
  · intro v
    rfl

theorem isDelta5Group_modO2Image {C L V : Subgroup G} (hLC : L ≤ C) (hVL : V ≤ L)
    (hEL : pCoreOf 2 L = pCoreOf 2 C ⊔ V) (hVn : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V)
    {α : ↥L →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L)
    {β : ↥V →* Multiplicative (evenWeight 5)} (hβs : Function.Surjective β)
    (hβk : β.ker = (pCoreOf 2 C ⊓ V).subgroupOf V)
    (hβeq : ∀ (x : ↥L) (v w : ↥V), (x : G) * (v : G) * (x : G)⁻¹ = (w : G) →
      ∀ i : Fin 5, ((Multiplicative.toAdd (β w) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2)
          (((α x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i)) :
    IsDelta5Group ↥(modO2Image C L) := by
  set ψ := imgHom hLC with hψdef
  have hψs : Function.Surjective ψ := imgHom_surjective hLC
  have hC_L : pCoreOf 2 C ≤ pCoreOf 2 L := by
    rw [hEL]
    exact le_sup_left
  have hle : ψ.ker ≤ α.ker := by
    intro x hx
    have h1 : x ∈ CFSG.pCore 2 ↥L :=
      (mem_pCore_iff_mem_pCoreOf_sub x).mpr (hC_L ((imgHom_eq_one_iff hLC x).mp (MonoidHom.mem_ker.mp hx)))
    show x ∈ α.ker
    rw [hαk]
    exact h1
  obtain ⟨αb, hαb⟩ := exists_comp_eq_of_surj_ker_le ψ hψs α hle
  have hαb_apply : ∀ x : ↥L, αb (ψ x) = α x := fun x => by
    rw [← hαb]
    rfl
  have hαbs : Function.Surjective αb := by
    intro y
    obtain ⟨x, hx⟩ := hαs y
    exact ⟨ψ x, (hαb_apply x).trans hx⟩
  have hpc : (CFSG.pCore 2 ↥L).map ψ = CFSG.pCore 2 ↥(modO2Image C L) := pCore_map_imgHom hLC
  have hαbk : αb.ker = CFSG.pCore 2 ↥(modO2Image C L) := by
    rw [← hpc]
    ext y
    obtain ⟨x, rfl⟩ := hψs y
    rw [MonoidHom.mem_ker, hαb_apply, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨x, ?_, rfl⟩
      rw [← hαk, MonoidHom.mem_ker]
      exact hx
    · rintro ⟨x', hx', hxx'⟩
      have hψeq : ψ x' = ψ x := hxx'
      have hα' : α x' = 1 := by
        have h1 : x' ∈ α.ker := by
          rw [hαk]
          exact hx'
        exact MonoidHom.mem_ker.mp h1
      calc α x = αb (ψ x) := (hαb_apply x).symm
        _ = αb (ψ x') := by rw [hψeq]
        _ = α x' := hαb_apply x'
        _ = 1 := hα'
  obtain ⟨Θc, hΘcs, hΘck, hΘc_apply⟩ := exists_pCore_image_iso hLC hVL hEL
  obtain ⟨e, he⟩ := exists_mulEquiv_comp_eq_of_surj_ker_eq Θc β hΘcs hβs (hΘck.trans hβk.symm)
  refine ⟨αb, e.toMonoidHom, hαbs, hαbk, e.bijective, ?_⟩
  intro x u v hv i
  obtain ⟨l, rfl⟩ := hψs x
  obtain ⟨a, rfl⟩ := hΘcs u
  obtain ⟨b, rfl⟩ := hΘcs v
  have hwV : (l : G) * (a : G) * (l : G)⁻¹ ∈ V := hVn l l.2 a a.2
  set w : ↥V := ⟨(l : G) * (a : G) * (l : G)⁻¹, hwV⟩ with hwdef
  have hlw : (l : ↥L) * Subgroup.inclusion hVL a * (l : ↥L)⁻¹ = Subgroup.inclusion hVL w := by
    apply Subtype.ext
    simp [hwdef]
  have h1 := hv
  rw [hΘc_apply, hΘc_apply] at h1
  have h2 : ψ l * imgHom hLC (Subgroup.inclusion hVL a) * (ψ l)⁻¹ =
      imgHom hLC ((l : ↥L) * Subgroup.inclusion hVL a * (l : ↥L)⁻¹) := by
    simp only [hψdef, map_mul, map_inv]
  rw [hlw] at h2
  have hΘb : imgHom hLC (Subgroup.inclusion hVL b) = imgHom hLC (Subgroup.inclusion hVL w) :=
    h1.trans h2
  have hbw : b⁻¹ * w ∈ β.ker := by
    rw [hβk, ← ker_imgHom_inclusion hLC hVL, MonoidHom.mem_ker, MonoidHom.comp_apply]
    simp only [map_mul, map_inv]
    rw [hΘb, inv_mul_cancel]
  have hβb : β b = β w := by
    rw [MonoidHom.mem_ker, map_mul, map_inv] at hbw
    exact inv_mul_eq_one.mp hbw
  simp only [MulEquiv.coe_toMonoidHom]
  rw [he b, he a, hαb_apply l, hβb]
  exact hβeq l a w rfl i

end Delta5

section Main

theorem ne_bot_of_D8 {G : Type} [Group G] {n : ℕ} (hn : 0 < n) {H : Subgroup G}
    (e : ↥H ≃* J4.D8CentralProduct n) : H ≠ ⊥ := by
  intro hH
  have h1 : Nat.card ↥H = 1 := by
    rw [hH]
    simp
  have h2 := Nat.card_congr e.toEquiv
  rw [h1, J4.card_D8CentralProduct hn] at h2
  have h3 : 1 < 2 ^ (2 * n + 1) := Nat.one_lt_two_pow (by omega)
  omega

theorem map_conj_centralizer_singleton {G : Type} [Group G] {z t : G}
    (ht : t ∈ Subgroup.centralizer ({z} : Set G)) :
    (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj t).toMonoidHom =
      Subgroup.centralizer ({z} : Set G) := by
  have hcomm : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp ht
  have hz' : z * t⁻¹ = t⁻¹ * z := by
    calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
      _ = t⁻¹ * (z * t) * t⁻¹ := by rw [hcomm]
      _ = t⁻¹ * z := by group
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    show t * c * t⁻¹ * z = z * (t * c * t⁻¹)
    calc t * c * t⁻¹ * z = t * c * (t⁻¹ * z) := by group
      _ = t * c * (z * t⁻¹) := by rw [← hz']
      _ = t * (c * z) * t⁻¹ := by group
      _ = t * (z * c) * t⁻¹ := by rw [hc']
      _ = (t * z) * c * t⁻¹ := by group
      _ = (z * t) * c * t⁻¹ := by rw [hcomm]
      _ = z * (t * c * t⁻¹) := by group
  · intro hx
    have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨t⁻¹ * x * t, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc t⁻¹ * x * t * z = t⁻¹ * x * (t * z) := by group
        _ = t⁻¹ * x * (z * t) := by rw [hcomm]
        _ = t⁻¹ * (x * z) * t := by group
        _ = t⁻¹ * (z * x) * t := by rw [hx']
        _ = (t⁻¹ * z) * x * t := by group
        _ = (z * t⁻¹) * x * t := by rw [hz']
        _ = z * (t⁻¹ * x * t) := by group
    · show t * (t⁻¹ * x * t) * t⁻¹ = x
      group

theorem map_le_normalizer_modO2Image {G : Type} [Group G] {C L T : Subgroup G} (hLC : L ≤ C)
    (hTC : T ≤ C) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    (T.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) ≤
      Subgroup.normalizer (modO2Image C L : Set (↥C ⧸ CFSG.pCore 2 ↥C)) := by
  have hsub : ∀ x ∈ (T.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C)),
      ∀ y ∈ modO2Image C L, x * y * x⁻¹ ∈ modO2Image C L := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨c, hc, rfl⟩
    refine ⟨t * c * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hcL : (c : G) ∈ L := Subgroup.mem_subgroupOf.mp hc
    exact (Subgroup.mem_normalizer_iff.mp (hTL htT) (c : G)).mp hcL
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => hsub x hx y hy
  · intro hy
    have h1 := hsub x⁻¹ (inv_mem hx) _ hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

end Main

theorem step8_2_13_insp_of
    (h8210 : Stmt8_2_10) (h8211 : Stmt8_2_11_modules) (h8212 : Stmt8_2_12) :
    Step8_2_13_insp := by
  intro G _ _ T L I hyp h731 h821 hc hrow hnot24 z hz hzV
  haveI : IsSimpleGroup G := hyp.fsu.simple
  obtain ⟨hcomp, hTLz, h4, hL34, hcode, hcocode⟩ :=
    h8211 G T L I hyp h731 h821 hc hrow hnot24 z hz hzV
  obtain ⟨-, hD, hEC, hEL, hVz⟩ := h8212 G T L I hyp h731 h821 hc hrow z hz hzV
  obtain ⟨hD34, hD22, hD24⟩ := hD
  have hV10 : fsuV T I = pCoreOf 2 L := (h8210 G T L I hyp h731 h821 hc hrow).2.1
  have hE1 : ch8E (fsuV T I) L z ≠ ⊥ := by
    rcases hrow with ⟨n, hn⟩ | h22 | h24 | h24'
    · obtain ⟨e⟩ := hD34 n hn
      exact ne_bot_of_D8 (by have := hn.1; omega) e
    · obtain ⟨e⟩ := hD22 h22
      exact ne_bot_of_D8 (by norm_num) e
    · exact absurd h24 hnot24
    · obtain ⟨⟨e⟩, -⟩ := hD24 h24'
      exact ne_bot_of_D8 (by norm_num) e
  rw [hEC] at hE1 hEL hVz
  have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
    (show z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) by
      rw [hzV]; exact Subgroup.mem_zpowers z).2
  have hzV' : z ∈ fsuV T I :=
    (show z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) by
      rw [hzV]; exact Subgroup.mem_zpowers z).1
  have hTC : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT t ht)
  have hVC : fsuV T I ≤ Subgroup.centralizer ({z} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance hv)) z hzV').symm
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hV10]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLzLC : ch8Lz L z ≤ L ⊓ Subgroup.centralizer ({z} : Set G) := fun l hl =>
    (CFSG.Quasithin.perfectCore_le (L ⊓ Subgroup.centralizer ({z} : Set G))) hl
  have hLzC : ch8Lz L z ≤ Subgroup.centralizer ({z} : Set G) := hLzLC.trans inf_le_right
  have hLzL : ch8Lz L z ≤ L := hLzLC.trans inf_le_left
  have hVn : ∀ l ∈ ch8Lz L z, ∀ v ∈ fsuV T I, l * v * l⁻¹ ∈ fsuV T I := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLN (hLzL hl)) v).mp hv
  have hVLz : fsuV T I ≤ ch8Lz L z := fun v hv =>
    (pCoreOf_le_self (ch8Lz L z)) (by rw [hEL]; exact Subgroup.mem_sup_right hv)
  have hTsyl : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) := by
    have hTtop : IsSylowTwoOf T ⊤ := ⟨le_top, hyp.fsu.sylow.1, by
      show ¬ 2 ∣ T.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hyp.fsu.sylow.2⟩
    exact CFSG.QuasithinUnique.isSylowTwoOf_of_le hTtop hTC
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hLM : L ≤ fsuM T L := (le_conjClosure L T).trans Subgroup.le_normalizer
  have hLzfam : ch8Lz L z ∈ lFamily T := by
    have hsub : ch8Lz L z ⊔ T ≤ fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) :=
      sup_le (le_inf (hLzL.trans hLM) hLzC) (le_inf hTM hTC)
    exact cComp_mem_of_le hcomp le_sup_left hsub
  have hKloc : LocalSQTK G :=
    (CFSG.QuasithinUnique.qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  obtain ⟨K, hKmem, hLzK⟩ := CFSG.QuasithinUnique.Vol2Native.lemma_1_2_4_exists hKloc
    CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
    CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved hE1 hTsyl hLzC hLzfam
  have hKT : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K := by
    intro t ht
    have hcC := map_conj_centralizer_singleton (hTC ht)
    have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp (Subgroup.centralizer ({z} : Set G)) := by
      have := CFSG.Quasithin.cComp_map_mulEquiv (MulAut.conj t) hKmem
      rwa [hcC] at this
    have h2 : ch8Lz L z ≤ K.map (MulAut.conj t).toMonoidHom := by
      intro l hl
      refine ⟨t⁻¹ * l * t, hLzK ?_, by show t * (t⁻¹ * l * t) * t⁻¹ = l; group⟩
      have := (Subgroup.mem_normalizer_iff.mp (hTLz (inv_mem ht)) l).mp hl
      simpa using this
    exact (CFSG.QuasithinUnique.Vol2Native.lemma_1_2_4_unique hKloc
      CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved hE1 hLzfam hKmem h1 hLzK h2).symm
  have hmem : ∀ t ∈ T, ∀ y : G, t * y * t⁻¹ ∈ K ↔ y ∈ K := by
    intro t ht y
    have h1 : (MulAut.conj t).toMonoidHom y ∈ K.map (MulAut.conj t).toMonoidHom ↔ y ∈ K :=
      Subgroup.mem_map_iff_mem (MulAut.conj t).injective
    rw [hKT t ht] at h1
    exact h1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff.mpr fun y => (hmem t ht y).symm
  have hconj : CFSG.Quasithin.conjClosure K T = K := le_antisymm
    (CFSG.Quasithin.conjClosure_le fun h hh z' hz' => (hmem h hh z').mpr hz')
    (CFSG.Quasithin.le_conjClosure K T)
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    have := CFSG.QuasithinUnique.Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKloc
      CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
      CFSG.Quasithin.Vol2.Ch10.SecA.a38ForSQTKCat_proved hE1 hTsyl hKmem
    rwa [hconj] at this
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := le_of_mem_cComp hKmem
  have hSQ := CFSG.QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKloc hE1
  have hTbar := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
    (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hTsyl) (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))))
    (QuotientGroup.mk'_surjective _)
  have hBbar := CFSG.Quasithin.modO2Image_mem_lFamily hTsyl hLzC hLzfam
  have hKbar := CFSG.Quasithin.modO2Image_mem_cComp hKmem
  have hBK : modO2Image (Subgroup.centralizer ({z} : Set G)) (ch8Lz L z) ≤
      modO2Image (Subgroup.centralizer ({z} : Set G)) K := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, Subgroup.mem_subgroupOf.mpr (hLzK (Subgroup.mem_subgroupOf.mp hc)), rfl⟩
  have hTNbar := map_le_normalizer_modO2Image hLzC hTC hTLz
  have hModO2 : Nat.card (ModO2 (modO2Image (Subgroup.centralizer ({z} : Set G)) (ch8Lz L z))) =
      Nat.card (↥(ch8Lz L z) ⧸ CFSG.pCore 2 ↥(ch8Lz L z)) := by
    obtain ⟨e⟩ := CFSG.Quasithin.Stellmacher.CD.L3YC.modO2_modO2Image_equiv hLzC
    exact Nat.card_congr e.toEquiv
  obtain ⟨Θc, hΘcs, hΘck, hΘc_apply⟩ := exists_pCore_image_iso hLzC hVLz hEL
  have hcocode' : Row711M24Cocode T L I := by
    rcases hrow with ⟨n, hn⟩ | h22 | h24 | h24'
    · exfalso
      have hn1 : n = 1 := h4 n hn
      subst hn1
      obtain ⟨α, β, hαs, hαk, hβs, hβk, hβeq⟩ := hL34 hn
      rw [hVz] at hβk
      exact Insp82.inspL34_holds _ hSQ _ hTbar _ hBbar hTNbar
        (isDelta5Group_modO2Image hLzC hVLz hEL hVn hαs hαk hβs hβk hβeq)
    · exfalso
      obtain ⟨h360, θ, hθs, hθk⟩ := hcode h22
      rw [hVz] at hθk
      obtain ⟨e5, -⟩ := exists_mulEquiv_comp_eq_of_surj_ker_eq Θc θ hΘcs hθs (hΘck.trans (by rw [hθk]))
      have hcard : Nat.card (CFSG.pCore 2 ↥(modO2Image (Subgroup.centralizer ({z} : Set G)) (ch8Lz L z))) = 2 ^ 5 := by
        rw [Nat.card_congr e5.toEquiv]
        simp [Nat.card_eq_fintype_card]
      exact Insp82.inspCode22_holds _ hSQ _ hTbar _ hBbar (hModO2.trans h360) hcard
    · exact absurd h24 hnot24
    · exact h24'
  obtain ⟨h1080, θ24, hθ24s, hθ24k⟩ := hcocode hcocode'
  rw [hVz] at hθ24k
  have hE16 : IsE2 4 ↥(CFSG.pCore 2 ↥(modO2Image (Subgroup.centralizer ({z} : Set G)) (ch8Lz L z))) := by
    obtain ⟨e4, -⟩ := exists_mulEquiv_comp_eq_of_surj_ker_eq Θc θ24 hΘcs hθ24s (hΘck.trans (by rw [hθ24k]))
    exact ⟨e4⟩
  obtain ⟨hq, hz3, hM⟩ := Insp82.inspCocode24_holds _ hSQ _ hTbar _ hKbar _ hBbar hBK (hModO2.trans h1080) hE16
  exact ⟨hcocode', K, hKC, hCN, hKmem, hLzK, hq, hz3, hM⟩

end CFSG.Quasithin.H13
