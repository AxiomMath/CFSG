module

public import CFSG.Quasithin.Vol2.Ch10SecBCoordPsi
public import CFSG.Quasithin.Vol2.Ch10SecABasicProd
public import CFSG.Quasithin.Vol2.Ch10SecBCoordL0
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

structure L0Coord (T L : Subgroup G) (t : G) (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ)
    (c : L32.Γ) : Prop where
  surj : Function.Surjective Ψ
  ker : ∀ y : ↥(fsuL0 T L), Ψ y = 1 ↔ (y : G) ∈ pCoreOf 2 (fsuL0 T L)
  hc : L32.IsU c
  onL : ∀ (l : G) (hl : l ∈ fsuL0 T L), l ∈ L → (Ψ ⟨l, hl⟩).2 = 1
  onLt : ∀ (l : G) (hl : l ∈ fsuL0 T L), l ∈ CFSG.conjugate L t → (Ψ ⟨l, hl⟩).1 = 1
  T0 : ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ = L32.U3.prod L32.U3
  swap : ∀ (y : ↥(fsuL0 T L)) (hy : t⁻¹ * y * t ∈ fsuL0 T L),
    Ψ ⟨t⁻¹ * y * t, hy⟩ = (c * (Ψ y).2 * c⁻¹, (Ψ y).1)
  T1act : ∀ s ∈ T1 T L, ∃ u v : L32.Γ, L32.IsU u ∧ L32.IsU v ∧
    ∀ (y : ↥(fsuL0 T L)) (hy : s * y * s⁻¹ ∈ fsuL0 T L),
      Ψ ⟨s * y * s⁻¹, hy⟩ = (u * (Ψ y).1 * u⁻¹, v * (Ψ y).2 * v⁻¹)

theorem mem_normalizer_conjugate (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {T L I : Subgroup G} (hyp : Hyp10 G T L I) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ T1 T L) :
    s ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  have hts : t * s ∉ Subgroup.normalizer (L : Set G) := fun h =>
    htn (by simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hs.2))
  rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate]
  exact SecA.conjugate_eq_of_not_mem h37 h38 hyp ht htn (T.mul_mem ht hs.1) hts

omit [Finite G] in
theorem quotO2Equiv_conjEquiv_mk {L : Subgroup G} (t : G) {l : G} (hl : l ∈ L)
    (hl' : t⁻¹ * l * t ∈ CFSG.conjugate L t) :
    quotO2Equiv (conjEquiv L t) (mkO2 L l hl) = mkO2 (CFSG.conjugate L t) (t⁻¹ * l * t) hl' := by
  rw [mkO2, quotO2Equiv_mk]
  congr 1
  exact Subtype.ext (conjEquiv_coe L t ⟨l, hl⟩)

omit [Finite G] in
theorem conj_mem_conjugate' {L : Subgroup G} (t : G) {l : G} (hl : l ∈ L) :
    t⁻¹ * l * t ∈ CFSG.conjugate L t := by
  rw [SecA.mem_conjugate_iff]
  simpa [mul_assoc] using hl

theorem exists_L0Coord
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {T L I : Subgroup G} (hyp : Hyp10 G T L I) (hL32 : LBarL32 L) (hinner : T1Inner T L)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ) (c : L32.Γ), L0Coord T L t Ψ c := by
  have hloc := hyp.fsu.maximal.1
  obtain ⟨φ, hφs, hφk, hφL, hφLt⟩ := SecA.exists_fsuL0_prod h37 h38 hyp ht htn
  obtain ⟨e⟩ := hL32
  obtain ⟨ψ1, hψ1⟩ := exists_equiv_map_eq_U3 e (isSylowTwoOf_D1 hyp)
  let θ := quotO2Equiv (conjEquiv L t)
  let ψ2 := θ.symm.trans ψ1
  let Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ := (ψ1.toMonoidHom.prodMap ψ2.toMonoidHom).comp φ
  have hΨ : ∀ y, Ψ y = (ψ1 (φ y).1, ψ2 (φ y).2) := fun _ => rfl
  have hΨL : ∀ (l : G) (hl : l ∈ L), Ψ ⟨l, SecA.le_fsuL0 T L hl⟩ = (ψ1 (mkO2 L l hl), 1) := by
    intro l hl
    rw [hΨ, hφL l hl]
    simp [ψ2]
  have hΨLt : ∀ (l : G) (hl : l ∈ L) (hl' : t⁻¹ * l * t ∈ fsuL0 T L),
      Ψ ⟨t⁻¹ * l * t, hl'⟩ = (1, ψ1 (mkO2 L l hl)) := by
    intro l hl hl'
    have hm := conj_mem_conjugate' t hl
    have h1 := hφLt _ hm
    rw [hΨ, show (⟨t⁻¹ * l * t, hl'⟩ : ↥(fsuL0 T L)) =
      ⟨t⁻¹ * l * t, SecA.conjugate_le_fsuL0 ht hm⟩ from rfl, h1]
    refine Prod.ext (by simp) ?_
    show ψ1 (θ.symm (mkO2 (CFSG.conjugate L t) _ hm)) = ψ1 (mkO2 L l hl)
    rw [← quotO2Equiv_conjEquiv_mk t hl hm, MulEquiv.symm_apply_apply]
  have hΨc : ∀ (y z : ↥(fsuL0 T L)), (y : G) = z → Ψ y = Ψ z := fun y z h =>
    congrArg Ψ (Subtype.ext h)
  clear_value Ψ
  have hL0eq := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  have hLle : L ≤ fsuL0 T L := SecA.le_fsuL0 T L
  have hLtle : CFSG.conjugate L t ≤ fsuL0 T L := fun x hx => SecA.conjugate_le_fsuL0 ht hx
  have hTN : ∀ s ∈ T, s ∈ Subgroup.normalizer (fsuL0 T L : Set G) := fun s hs => SecA.le_fsuM T L hs
  have ht2 : t⁻¹ * t⁻¹ ∈ T1 T L := by
    refine ⟨T.mul_mem (T.inv_mem ht) (T.inv_mem ht), ?_⟩
    have := Subgroup.inv_mem _ (SecA.mul_self_mem_normalizer h37 h38 hyp ht htn)
    simpa [mul_inv_rev] using this
  obtain ⟨c, hc, hcx⟩ := exists_inner_coord hinner ψ1 hψ1 ht2
  have hLt_iff : ∀ {x : G}, x ∈ CFSG.conjugate L t ↔ t * x * t⁻¹ ∈ L := SecA.mem_conjugate_iff
  refine ⟨Ψ, c, ⟨fun p => ?_, fun y => ?_, hc, fun l hl0 hl => ?_, fun l hl0 hl => ?_, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨y, hy⟩ := hφs (ψ1.symm p.1, ψ2.symm p.2)
    exact ⟨y, by rw [hΨ, hy]; simp⟩
  ·
    rw [hΨ, Prod.mk_eq_one, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← Prod.mk_eq_one,
      Prod.mk.eta, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  ·
    rw [hΨc ⟨l, hl0⟩ ⟨l, hLle hl⟩ rfl, hΨL l hl]
  ·
    have hl' := hLt_iff.mp hl
    have h1 := hΨLt (t * l * t⁻¹) hl' (by simpa [mul_assoc] using hl0)
    rw [hΨc ⟨l, hl0⟩ ⟨t⁻¹ * (t * l * t⁻¹) * t, by simpa [mul_assoc] using hl0⟩ (by group), h1]
  ·
    have hT0L0 : T0 T L ≤ fsuL0 T L := inf_le_right
    have hge : L32.U3.prod L32.U3 ≤ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      rw [← hψ1] at ha hb
      obtain ⟨_, ⟨⟨d₁, hd₁L⟩, hd₁, rfl⟩, rfl⟩ := ha
      obtain ⟨_, ⟨⟨d₂, hd₂L⟩, hd₂, rfl⟩, rfl⟩ := hb
      have hd₁T : d₁ ∈ T := (Subgroup.mem_subgroupOf.mp hd₁).1
      have hd₂T : d₂ ∈ T := (Subgroup.mem_subgroupOf.mp hd₂).1
      have hm₂ : t⁻¹ * d₂ * t ∈ fsuL0 T L := hLtle (conj_mem_conjugate' t hd₂L)
      refine ⟨⟨d₁ * (t⁻¹ * d₂ * t), (fsuL0 T L).mul_mem (hLle hd₁L) hm₂⟩,
        Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem hd₁T (T.mul_mem (T.mul_mem (T.inv_mem ht) hd₂T) ht),
          (fsuL0 T L).mul_mem (hLle hd₁L) hm₂⟩, ?_⟩
      rw [show (⟨d₁ * (t⁻¹ * d₂ * t), (fsuL0 T L).mul_mem (hLle hd₁L) hm₂⟩ : ↥(fsuL0 T L)) =
        ⟨d₁, hLle hd₁L⟩ * ⟨t⁻¹ * d₂ * t, hm₂⟩ from rfl, map_mul, hΨL d₁ hd₁L, hΨLt d₂ hd₂L hm₂]
      simp
    have hp : IsPGroup 2 (((T0 T L).subgroupOf (fsuL0 T L)).map Ψ) := by
      have h2 : IsPGroup 2 (T0 T L) := hyp.fsu.sylow.1.to_le inf_le_left
      exact (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hT0L0).symm).map Ψ
    exact eq_U3_prod_of_le hp hge
  ·
    have htN : t⁻¹ ∈ Subgroup.normalizer (fsuL0 T L : Set G) := Subgroup.inv_mem _ (hTN t ht)
    have hfg : Ψ.comp (conjHom (fsuL0 T L) htN) = (twistSwap c).comp Ψ := by
      refine hom_ext_of_sup hLle hLtle hL0eq.symm (fun l hl => ?_) (fun l hl => ?_)
      · have hm : t⁻¹ * l * t ∈ fsuL0 T L := hLtle (conj_mem_conjugate' t hl)
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twistSwap_apply, hΨL l hl,
          hΨc _ ⟨t⁻¹ * l * t, hm⟩ (by rw [conjHom_coe, inv_inv]), hΨLt l hl hm]
        simp
      · have hl' := hLt_iff.mp hl
        have hm2 : t⁻¹ * t⁻¹ * (t * l * t⁻¹) * (t⁻¹ * t⁻¹)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp ht2.2 _).mp hl'
        have hm : t⁻¹ * (t * l * t⁻¹) * t ∈ fsuL0 T L := by simpa [mul_assoc] using hLtle hl
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twistSwap_apply,
          hΨc _ ⟨_, hLle hm2⟩ (by rw [conjHom_coe]; group), hΨL _ hm2, hcx _ hl',
          hΨc ⟨l, hLtle hl⟩ ⟨_, hm⟩ (by group), hΨLt _ hl' hm]
    intro y hy
    have h := congrArg (fun f => f y) hfg
    simp only [MonoidHom.comp_apply, twistSwap_apply] at h
    rw [← h]
    exact hΨc _ _ (by rw [conjHom_coe, inv_inv])
  ·
    intro s hs
    have hsN : s ∈ Subgroup.normalizer (fsuL0 T L : Set G) := hTN s hs.1
    obtain ⟨u, hu, hux⟩ := exists_inner_coord hinner ψ1 hψ1 hs
    have hsLt := mem_normalizer_conjugate h37 h38 hyp ht htn hs
    have hs'' : t * s * t⁻¹ ∈ T1 T L := by
      refine ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht), Subgroup.mem_normalizer_iff.mpr ?_⟩
      intro x
      have e1 : x ∈ L ↔ t⁻¹ * x * t ∈ CFSG.conjugate L t := by
        rw [hLt_iff]; simp [mul_assoc]
      have e3 : s * (t⁻¹ * x * t) * s⁻¹ ∈ CFSG.conjugate L t ↔
          t * s * t⁻¹ * x * (t * s * t⁻¹)⁻¹ ∈ L := by
        rw [hLt_iff]
        constructor <;> intro h <;> convert h using 1 <;> group
      exact e1.trans ((Subgroup.mem_normalizer_iff.mp hsLt _).trans e3)
    obtain ⟨v, hv, hvx⟩ := exists_inner_coord hinner ψ1 hψ1 hs''
    refine ⟨u, v, hu, hv, ?_⟩
    have hfg : Ψ.comp (conjHom (fsuL0 T L) hsN) = (conjPair u v).comp Ψ := by
      refine hom_ext_of_sup hLle hLtle hL0eq.symm (fun l hl => ?_) (fun l hl => ?_)
      · have hsl : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hs.2 l).mp hl
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conjPair_apply, hΨL l hl,
          hΨc _ ⟨s * l * s⁻¹, hLle hsl⟩ (conjHom_coe _ _ _), hΨL _ hsl, hux l hl]
        simp
      · have hl' := hLt_iff.mp hl
        have hm : t * s * t⁻¹ * (t * l * t⁻¹) * (t * s * t⁻¹)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp hs''.2 _).mp hl'
        have hm' : t⁻¹ * (t * s * t⁻¹ * (t * l * t⁻¹) * (t * s * t⁻¹)⁻¹) * t ∈ fsuL0 T L :=
          hLtle (conj_mem_conjugate' t hm)
        have hl0 : t⁻¹ * (t * l * t⁻¹) * t ∈ fsuL0 T L := by simpa [mul_assoc] using hLtle hl
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conjPair_apply,
          hΨc _ ⟨_, hm'⟩ (by rw [conjHom_coe]; group), hΨLt _ hm hm', hvx _ hl',
          hΨc ⟨l, hLtle hl⟩ ⟨_, hl0⟩ (by group), hΨLt _ hl' hl0]
        simp
    intro y hy
    have h := congrArg (fun f => f y) hfg
    simp only [MonoidHom.comp_apply, conjPair_apply] at h
    rw [← h]
    exact hΨc _ _ (conjHom_coe _ _ _).symm

end CFSG.Quasithin.Vol2.Ch10.SecB
