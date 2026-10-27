module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.F918T3
public import CFSG.Quasithin.Background.SmithA36
import CFSG.Quasithin.Background.InternalSecIrr
import CFSG.Quasithin.Background.B69Red

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Kernel

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

@[expose] noncomputable def rho (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) : ↥Lb →* MulAut ↥Vb :=
  resHomOn Vb (z35_le_stabSub hZ hML)

theorem rho_apply (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (l : ↥Lb) (v : ↥Vb) :
    ((rho hZ hML l v : ↥Vb) : X) = (l : MulAut X) v := rfl

theorem mem_ker_rho (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (l : ↥Lb) :
    l ∈ (rho hZ hML).ker ↔ ∀ v ∈ Vb, (l : MulAut X) v = v := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v hv
    have h2 : (rho hZ hML l) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [h]; rfl
    exact congrArg Subtype.val h2
  · intro h
    refine MulEquiv.ext fun v => Subtype.ext ?_
    exact h v v.2

theorem conj_inv_mem (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {s : MulAut X} (hs : s ∈ Tb)
    {l : MulAut X} (hl : l ∈ Lb) : s⁻¹ * l * s ∈ Lb := by
  simpa using z35_conj_mem hZ hML (Tb.inv_mem hs) hl

theorem eq_one_of_conj_mem_ker (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (l : ↥Lb)
    (h : ∀ s ∈ Tb, ∀ hl : s⁻¹ * (l : MulAut X) * s ∈ Lb,
      (⟨s⁻¹ * (l : MulAut X) * s, hl⟩ : ↥Lb) ∈ (rho hZ hML).ker) : l = 1 := by
  let U : Subgroup X := MonoidHom.eqLocus (l : MulAut X).toMonoidHom (MonoidHom.id X)
  have hU : orbSup Tb Vb ≤ U := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hk := (mem_ker_rho hZ hML _).mp (h s hs (conj_inv_mem hZ hML hs l.2)) v hv
    show (l : MulAut X) (s v) = s v
    have e : (l : MulAut X) (s v) = s ((s⁻¹ * (l : MulAut X) * s) v) := by
      simp [MulAut.mul_apply]
    rw [e, hk]
  have htop : ∀ x : X, (l : MulAut X) x = x := by
    intro x
    have hx : x ∈ orbSup Tb Vb := by rw [hZ.gen]; trivial
    exact hU hx
  exact Subtype.ext (MulEquiv.ext htop)

theorem ker_rho_central (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {l : ↥Lb}
    (hl : l ∈ (rho hZ hML).ker) : l ∈ Subgroup.center ↥Lb := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext
    (z35_central_of_trivial hZ hML l.2 ((mem_ker_rho hZ hML l).mp hl) g g.2).symm

theorem conj_inv_central (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {s : MulAut X} (hs : s ∈ Tb)
    {l : ↥Lb} (hl : l ∈ Subgroup.center ↥Lb) :
    (⟨s⁻¹ * (l : MulAut X) * s, conj_inv_mem hZ hML hs l.2⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
  rw [Subgroup.mem_center_iff] at hl ⊢
  intro g
  have h1 := hl ⟨s * (g : MulAut X) * s⁻¹, z35_conj_mem hZ hML hs g.2⟩
  have h2 : (s * (g : MulAut X) * s⁻¹) * (l : MulAut X) =
      (l : MulAut X) * (s * (g : MulAut X) * s⁻¹) :=
    congrArg Subtype.val h1
  refine Subtype.ext ?_
  show (g : MulAut X) * (s⁻¹ * (l : MulAut X) * s) = s⁻¹ * (l : MulAut X) * s * g
  calc (g : MulAut X) * (s⁻¹ * (l : MulAut X) * s)
      = s⁻¹ * ((s * (g : MulAut X) * s⁻¹) * (l : MulAut X)) * s := by group
    _ = s⁻¹ * ((l : MulAut X) * (s * (g : MulAut X) * s⁻¹)) * s := by rw [h2]
    _ = s⁻¹ * (l : MulAut X) * s * (g : MulAut X) := by group

theorem rho_mem_autSub (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (l : ↥Lb) :
    rho hZ hML l ∈ autSub Lb Vb := by
  rw [autSub_eq_range_resHomOn (z35_le_stabSub hZ hML)]
  exact ⟨l, rfl⟩

theorem exists_rho_eq (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {φ : MulAut ↥Vb}
    (h : φ ∈ autSub Lb Vb) : ∃ g : ↥Lb, rho hZ hML g = φ := by
  have h' : φ ∈ (resHomOn Vb (z35_le_stabSub hZ hML)).range := by
    rwa [← autSub_eq_range_resHomOn (z35_le_stabSub hZ hML)]
  exact h'

@[expose] noncomputable def rho' (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    ↥Lb →* ↥(autSub Lb Vb) :=
  (rho hZ hML).codRestrict (autSub Lb Vb) (rho_mem_autSub hZ hML)

theorem rho'_surjective (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    Function.Surjective (rho' hZ hML) := by
  intro y
  obtain ⟨l, hl⟩ := exists_rho_eq hZ hML y.2
  exact ⟨l, Subtype.ext hl⟩

theorem rho'_apply (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (l : ↥Lb) :
    ((rho' hZ hML l : ↥(autSub Lb Vb)) : MulAut ↥Vb) = rho hZ hML l := rfl

theorem ker_rho' (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    (rho' hZ hML).ker = (rho hZ hML).ker := by
  ext l
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem rho'_injective_iff (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    Function.Injective (rho' hZ hML) ↔ Function.Injective (rho hZ hML) := by
  rw [injective_iff_map_eq_one, injective_iff_map_eq_one]
  constructor
  · intro h l hl
    exact h l (Subtype.ext hl)
  · intro h l hl
    exact h l (congrArg Subtype.val hl)

theorem isQuasisimple_autSub_Lb (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    CFSG.IsQuasisimple ↥(autSub Lb Vb) := by
  obtain ⟨l, hl, v, hv, hlv⟩ := hZ.nontriv 1 Tb.one_mem
  obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := rho' hZ hML) hZ.quasi
    (rho'_surjective hZ hML) ⟨⟨l', hl'⟩, fun h1 => hlv ?_⟩
  have h2 : rho hZ hML ⟨l', hl'⟩ = 1 := congrArg Subtype.val h1
  have := congrArg (fun φ : MulAut ↥Vb => ((φ ⟨v, hv⟩ : ↥Vb) : X)) h2
  simpa [rho_apply, MulAut.conj_apply] using this

theorem isIrrSec_autSub_Lb (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    XMod.IsIrrSec ↥(autSub Lb Vb) (⊥ : Subgroup ↥Vb) ⊤ := by
  have hLs := z35_le_stabSub hZ hML
  have hirr : XMod.IsIrr ↥Lb Vb := hML ▸ hZ.irr
  obtain ⟨-, hlt, hJ⟩ := hirr
  refine ⟨?_, fun J hJinv _ _ => ?_⟩
  · obtain ⟨u, hu, hu1⟩ := IsConcreteLE.exists_of_lt hlt
    refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨bot_le, ⟨u, hu⟩, trivial, fun h1 => hu1 ?_⟩
    rw [Subgroup.mem_bot] at h1 ⊢
    exact congrArg Subtype.val h1
  · have hinv : XMod.IsInv ↥Lb (J.map Vb.subtype) := by
      rintro ⟨a, ha⟩ _ ⟨w, hw, rfl⟩
      exact ⟨resHom Vb ⟨a, hLs ha⟩ w,
        hJinv ⟨resHom Vb ⟨a, hLs ha⟩, mem_autSub.mpr ⟨⟨a, hLs ha⟩, ha, rfl⟩⟩ w hw, rfl⟩
    rcases hJ (J.map Vb.subtype) hinv bot_le (Subgroup.map_subtype_le J) with h1 | h1
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ Vb.subtype_injective).mp h1
    · right
      rw [eq_top_iff]
      intro u _
      have hu : (u : X) ∈ J.map Vb.subtype := by rw [h1]; exact u.2
      exact (Subgroup.mem_map_iff_mem (x := u) Vb.subtype_injective).mp hu

theorem ker_rho_odd (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) :
    ∀ z ∈ (rho hZ hML).ker, Odd (orderOf z) := by
  have hexp : ∀ w : ↥Vb, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hZ.exp])
  have hq := isQuasisimple_autSub_Lb hZ hML
  have hirr := isIrrSec_autSub_Lb hZ hML
  have hodd : Odd (Nat.card ↥(XMod.eqvAut ↥(autSub Lb Vb) ↥Vb)) :=
    InternalSec.odd_card_eqvAut_of_irr hexp hirr
      (InternalSec.exists_noncomm_of_isQuasisimple hq)
  intro z hz
  by_contra hev
  have h2dvd : 2 ∣ orderOf z := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  have hz0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  set z' : ↥Lb := z ^ (orderOf z / 2) with hz'def
  have hz'ord : orderOf z' = 2 := orderOf_pow_orderOf_div hz0 h2dvd
  have hz'ker : z' ∈ (rho hZ hML).ker := Subgroup.pow_mem _ hz _
  have hz'2 : (z' : MulAut X) * (z' : MulAut X) = 1 := by
    have h1 : z' ^ 2 = 1 := by rw [← hz'ord]; exact pow_orderOf_eq_one z'
    have h2 := congrArg Subtype.val h1
    simpa [pow_two] using h2
  have hz'c : z' ∈ Subgroup.center ↥Lb := ker_rho_central hZ hML hz'ker
  have hconj : ∀ s ∈ Tb, ∀ hl : s⁻¹ * (z' : MulAut X) * s ∈ Lb,
      (⟨s⁻¹ * (z' : MulAut X) * s, hl⟩ : ↥Lb) ∈ (rho hZ hML).ker := by
    intro s hs hl
    set zs : ↥Lb := ⟨s⁻¹ * (z' : MulAut X) * s, hl⟩ with hzs
    have hzsc : zs ∈ Subgroup.center ↥Lb := conj_inv_central hZ hML hs hz'c
    have hzs2 : zs * zs = 1 := by
      refine Subtype.ext ?_
      show s⁻¹ * (z' : MulAut X) * s * (s⁻¹ * (z' : MulAut X) * s) = 1
      calc s⁻¹ * (z' : MulAut X) * s * (s⁻¹ * (z' : MulAut X) * s)
          = s⁻¹ * ((z' : MulAut X) * (z' : MulAut X)) * s := by group
        _ = 1 := by rw [hz'2]; group
    have hmem : rho hZ hML zs ∈ XMod.eqvAut ↥(autSub Lb Vb) ↥Vb := by
      intro a p
      obtain ⟨g, hg⟩ : ∃ g : ↥Lb, rho hZ hML g = (a : MulAut ↥Vb) :=
        exists_rho_eq hZ hML a.2
      have hcg : zs * g = g * zs := (Subgroup.mem_center_iff.mp hzsc g).symm
      change rho hZ hML zs ((a : MulAut ↥Vb) p) = (a : MulAut ↥Vb) (rho hZ hML zs p)
      rw [← hg]
      have := congrArg (fun l : ↥Lb => rho hZ hML l p) hcg
      simpa [map_mul] using this
    let φ : ↥(XMod.eqvAut ↥(autSub Lb Vb) ↥Vb) := ⟨rho hZ hML zs, hmem⟩
    have hφ2 : φ ^ 2 = 1 := by
      refine Subtype.ext ?_
      show rho hZ hML zs * rho hZ hML zs = 1
      rw [← map_mul, hzs2, map_one]
    have hord : orderOf φ = 1 := by
      have h1 : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one hφ2
      have h2 : orderOf φ ∣ Nat.card ↥(XMod.eqvAut ↥(autSub Lb Vb) ↥Vb) := orderOf_dvd_natCard _
      exact Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h1 h2
    have hφ1 : φ = 1 := orderOf_eq_one_iff.mp hord
    have := congrArg Subtype.val hφ1
    exact this
  have h1 : z' = 1 := eq_one_of_conj_mem_ker hZ hML z' hconj
  rw [h1, orderOf_one] at hz'ord
  omega

theorem rho_injective_of_center_bot (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hc : Subgroup.center ↥(autSub Lb Vb) = ⊥) : Function.Injective (rho hZ hML) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hlker : l ∈ (rho hZ hML).ker := hl
  refine eq_one_of_conj_mem_ker hZ hML l fun s hs hl' => ?_
  set zs : ↥Lb := ⟨s⁻¹ * (l : MulAut X) * s, hl'⟩ with hzs
  have hzsc : zs ∈ Subgroup.center ↥Lb :=
    conj_inv_central hZ hML hs (ker_rho_central hZ hML hlker)
  have hcen : (⟨rho hZ hML zs, rho_mem_autSub hZ hML zs⟩ : ↥(autSub Lb Vb)) ∈
      Subgroup.center ↥(autSub Lb Vb) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, hg⟩ := exists_rho_eq hZ hML y.2
    refine Subtype.ext ?_
    show (y : MulAut ↥Vb) * rho hZ hML zs = rho hZ hML zs * (y : MulAut ↥Vb)
    rw [← hg, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzsc g]
  rw [hc, Subgroup.mem_bot] at hcen
  exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hcen)

theorem rho_injective_of_isL345 (hA21 : AsA21SQTKSection) (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (h : IsL345Type ↥(autSub Lb Vb)) : Function.Injective (rho hZ hML) := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hZ.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hLX : Lb ≤ Mb ⊔ Tb := hML ▸ le_sup_left
  have hSL : SQTKGroup ↥Lb := B69.sqtk_subgroup hA21 hS φ hφ hLX hZ.quasi
  have hinj := asA36NoOddCover_holds ↥Lb ↥(autSub Lb Vb) hZ.quasi hSL (rho' hZ hML)
    (rho'_surjective hZ hML) (by rw [ker_rho']; exact ker_rho_odd hZ hML) h
  exact (rho'_injective_iff hZ hML).mp hinj

theorem rho_injective_of_hatA6 (hhat : NoOddCoverHatA6) (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (h : Nat.card (Subgroup.center ↥(autSub Lb Vb)) = 3 ∧
      Nonempty (↥(autSub Lb Vb) ⧸ Subgroup.center ↥(autSub Lb Vb) ≃*
        ↥(alternatingGroup (Fin 6)))) : Function.Injective (rho hZ hML) := by
  have hinj := hhat ↥Lb ↥(autSub Lb Vb) hZ.quasi h.1 h.2 (rho' hZ hML) (rho'_surjective hZ hML)
    (by rw [ker_rho']; exact ker_rho_odd hZ hML)
  exact (rho'_injective_iff hZ hML).mp hinj

theorem rho_injective (hA21 : AsA21SQTKSection) (hhat : NoOddCoverHatA6)
    (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) (hc : CentralData (autSub Lb Vb)) :
    Function.Injective (rho hZ hML) := by
  rcases hc with h | h | h
  · exact rho_injective_of_center_bot hZ hML h
  · exact rho_injective_of_isL345 hA21 hZ hML h
  · exact rho_injective_of_hatA6 hhat hZ hML h

end Kernel

end CFSG.Quasithin.F918X
