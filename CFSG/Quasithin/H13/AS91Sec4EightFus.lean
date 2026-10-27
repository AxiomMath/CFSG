module

public import CFSG.Quasithin.Vol2.Asc94.TS39b
public import CFSG.Quasithin.H13.AS91Sec4EightRec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

theorem okRows_rowsOf (U : V12 ≃ₗ[ZMod 2] V12) : okRows (rowsOf U) = true := by
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq]
  exact ⟨rowsOf_size U, fun x hx => rowsOf_lt U x hx⟩

theorem rowsOf_mul (U V : V12 ≃ₗ[ZMod 2] V12) : rowsOf (U * V) = mulR (rowsOf U) (rowsOf V) :=
  rowsOf_eq (okRows_mulR (okRows_rowsOf U) (okRows_rowsOf V)) fun v => by
    rw [LinearEquiv.mul_apply, linOfRows_mulR, linOfRows_rowsOf, linOfRows_rowsOf]

theorem rowsOf_injective : Function.Injective rowsOf := fun U V h =>
  LinearEquiv.ext fun v => by rw [← linOfRows_rowsOf U v, h, linOfRows_rowsOf]

namespace Two

theorem r7Gens_sub : ∀ g ∈ r7Gens, g ∈ c3List () := fun g hg => by
  obtain ⟨-, -, -, -, -, -, -, hok, hid, hcl, -, hT, -⟩ := tOK48_spec
  exact t7List_sub_c3List (hT g (mem_enum7_of_mem_gens hok hid hcl hg))

theorem fusOK48_spec :
    ((enum7 r7Gens).filter fun X => X != id7 && (enumGrp (stabGens48 ())).any fun r =>
      res6 r == aPart X && decide (128 ≤ fix7 X * fixEb r)).dedup.length ≤ 27 := by
  have h := ok48_parts.2.2.2.2.2.1
  simpa only [fusOK48, decide_eq_true_eq] using h

theorem aPart_mk7 {A : List ℕ} (hA : A.length = 6) (l : ℕ) : aPart (mk7 l A) = A := by
  have e : aPart (mk7 l A) = (List.range 6).map fun i => ((l >>> i) % 2 + 2 * A.getD i 0) / 2 := by
    simp [aPart, mk7, List.map_map, Function.comp_def]
  rw [e]
  apply List.ext_getElem
  · simp [hA]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega)]
    omega

end Two

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section CE


@[expose] noncomputable def cE (φ : ↥D.Mb) : Subgroup ↥D.E :=
  ((φ : MulAut ↥D.E) : ↥D.E →* ↥D.E).eqLocus (MonoidHom.id ↥D.E)

theorem mem_cE {φ : ↥D.Mb} {x : ↥D.E} : x ∈ D.cE φ ↔ (φ : MulAut ↥D.E) x = x := Iff.rfl

theorem card_cE_conj (g φ : ↥D.Mb) : Nat.card (D.cE (g * φ * g⁻¹)) = Nat.card (D.cE φ) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((g⁻¹ : ↥D.Mb) : MulAut ↥D.E) x, ?_⟩
      invFun := fun x => ⟨(g : MulAut ↥D.E) x, ?_⟩
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun x => Subtype.ext ?_ }
  · rw [mem_cE]
    have hx := D.mem_cE.mp x.2
    change ((g * φ * g⁻¹ : ↥D.Mb) : MulAut ↥D.E) x = x at hx
    calc (φ : MulAut ↥D.E) (((g⁻¹ : ↥D.Mb) : MulAut ↥D.E) x)
        = ((g⁻¹ : ↥D.Mb) : MulAut ↥D.E) (((g * φ * g⁻¹ : ↥D.Mb) : MulAut ↥D.E) x) := by
          change _ = (((g⁻¹ * (g * φ * g⁻¹)) : ↥D.Mb) : MulAut ↥D.E) x
          rw [show g⁻¹ * (g * φ * g⁻¹) = φ * g⁻¹ by group]
          rfl
      _ = _ := by rw [hx]
  · rw [mem_cE]
    have hx := D.mem_cE.mp x.2
    change (((g * φ * g⁻¹) * g : ↥D.Mb) : MulAut ↥D.E) x = (g : MulAut ↥D.E) x
    rw [show g * φ * g⁻¹ * g = g * φ by group]
    change (g : MulAut ↥D.E) ((φ : MulAut ↥D.E) x) = _
    rw [hx]
  · change (((g * g⁻¹ : ↥D.Mb)) : MulAut ↥D.E) x = x
    rw [mul_inv_cancel]
    rfl
  · change (((g⁻¹ * g : ↥D.Mb)) : MulAut ↥D.E) x = x
    rw [inv_mul_cancel]
    rfl

end CE

section CEt

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem ncard_Iset : D.Iset.ncard = 16 := by
  have hI : D.Iset = D.omE '' ↑Two.i7List.toFinset := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxE1, hxc⟩ := (D.mem_Iset_iff hOut hTw hHat x).mp hx
      exact ⟨D.crd x, List.mem_toFinset.mpr hxc, Subtype.ext (D.elt7_crd hxE1)⟩
    · rintro ⟨c, hc, rfl⟩
      exact D.omE_mem_Iset hOut hTw hHat (List.mem_toFinset.mp hc)
  have hinj : Set.InjOn D.omE ↑Two.i7List.toFinset := fun a ha b hb hab =>
    D.elt7_injective (Two.i7List_lt a (List.mem_toFinset.mp ha))
      (Two.i7List_lt b (List.mem_toFinset.mp hb)) (congrArg Subtype.val hab)
  rw [hI, hinj.ncard_image, Set.ncard_coe_finset]
  decide

theorem card_cE_tb : Nat.card (D.cE D.tb) = 128 := by
  have hc : ∀ a b : ↥D.E, a * b = b * a := fun a b =>
    Subtype.ext (D.E_comm hOut hTw hHat a.2 b.2)
  let f : ↥D.E →* ↥D.E :=
    { toFun := fun e => e⁻¹ * (D.tb : MulAut ↥D.E) e
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * ((D.tb : MulAut ↥D.E) a * (D.tb : MulAut ↥D.E) b) =
            a⁻¹ * (b⁻¹ * (D.tb : MulAut ↥D.E) a) * (D.tb : MulAut ↥D.E) b := by
              rw [hc b⁻¹ a⁻¹]; group
          _ = a⁻¹ * ((D.tb : MulAut ↥D.E) a * b⁻¹) * (D.tb : MulAut ↥D.E) b := by rw [hc b⁻¹]
          _ = _ := by group }
  have hker : f.ker = D.cE D.tb := by
    ext e
    rw [MonoidHom.mem_ker, mem_cE]
    change e⁻¹ * (D.tb : MulAut ↥D.E) e = 1 ↔ _
    rw [inv_mul_eq_one, eq_comm]
  have hrange : (f.range : Set ↥D.E) = D.Iset := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker, D.card_E hOut hTw] at h1
  have h2 : Nat.card f.range = 16 := by
    rw [← D.ncard_Iset hOut hTw hHat, ← hrange, ← Nat.card_coe_set_eq]
    rfl
  rw [h2] at h1
  omega

end CEt

section Bound

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem card_cE_le {m : G} (hmN : m ∈ normalizer (D.E : Set G)) (hmM : m ∈ h.setting.M)
    (hz : D.toMb ⟨m, hmN⟩ ∈ D.Mz) :
    Nat.card (D.cE (D.toMb ⟨m, hmN⟩)) ≤
      Two.fix7 (D.kap (D.toMb ⟨m, hmN⟩ : MulAut ↥D.E)) *
        Two.fixEb (rowsOf (D.Φo (h.setting.ρ ⟨m, hmM⟩))) := by
  set φ := D.toMb ⟨m, hmN⟩ with hφ
  set R := D.Φo (h.setting.ρ ⟨m, hmM⟩) with hR
  have hp := D.presE1_of_mem_Mz hOut hTw hz
  let π : ↥(D.cE φ) →* (V12 ≃ₗ[ZMod 2] V12) :=
    D.Φo.comp (h.setting.ρ.comp ((Subgroup.inclusion D.E_le_M).comp (D.cE φ).subtype))
  have hπ : ∀ x : ↥(D.cE φ), π x = D.Φo (h.setting.ρ ⟨((x : ↥D.E) : G), D.E_le_M (x : ↥D.E).2⟩) :=
    fun _ => rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv] at h1
  have hker : Nat.card π.ker ≤ Two.fix7 (D.kap (φ : MulAut ↥D.E)) := by
    have hmemE1 : ∀ x : ↥π.ker, (((x : ↥(D.cE φ)) : ↥D.E) : G) ∈ D.E1 := by
      intro x
      have hx := MonoidHom.mem_ker.mp x.2
      rw [hπ] at hx
      have h2 : h.setting.ρ ⟨_, D.E_le_M ((x : ↥(D.cE φ)) : ↥D.E).2⟩ = 1 :=
        D.Φo_injective (hx.trans (map_one _).symm)
      exact D.mem_E1_of_mem_E ((h.setting.ρ_eq_one_iff _).mp h2) ((x : ↥(D.cE φ)) : ↥D.E).2
    let f : ↥π.ker → ↥((List.range 128).filter fun v => Two.app7 (D.kap (φ : MulAut ↥D.E)) v == v).toFinset :=
      fun x => ⟨D.crd (((x : ↥(D.cE φ)) : ↥D.E) : G), by
        rw [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq]
        refine ⟨D.crd_lt _ (hmemE1 x), ?_⟩
        rw [← D.crd_apply hp (hmemE1 x), D.mem_cE.mp (x : ↥(D.cE φ)).2]⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (D.crd_injective (hmemE1 x) (hmemE1 y) (congrArg Subtype.val hxy))))
    calc Nat.card π.ker ≤ Nat.card ↥((List.range 128).filter fun v =>
          Two.app7 (D.kap (φ : MulAut ↥D.E)) v == v).toFinset := Nat.card_le_card_of_injective f hf
      _ = _ := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, Two.fix7]
        exact List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)
  have hrange : Nat.card π.range ≤ Two.fixEb (rowsOf R) := by
    obtain ⟨-, -, -, -, hid, hc, -⟩ := Two.ebOK46_spec
    have hmemU : ∀ U : ↥π.range, rowsOf (U : V12 ≃ₗ[ZMod 2] V12) ∈
        (enumGrp Two.ebRows).filter fun e => mulR (rowsOf R) e == mulR e (rowsOf R) := by
      rintro ⟨_, x, rfl⟩
      change rowsOf (π x) ∈ _
      rw [hπ]
      have hU := D.Φo_mem_eb hOut hTw ((x : ↥D.E)).2 (D.E_le_M (x : ↥D.E).2)
      obtain ⟨r, hr, hUr⟩ := complete hid hc _ hU
      have hrU := rowsOf_eq (enumGrp_sound Two.gensOK_eb r hr).1 hUr
      refine List.mem_filter.mpr ⟨hrU ▸ hr, beq_iff_eq.mpr ?_⟩
      have hcomm : R * D.Φo (h.setting.ρ ⟨((x : ↥D.E) : G), D.E_le_M (x : ↥D.E).2⟩) =
          D.Φo (h.setting.ρ ⟨((x : ↥D.E) : G), D.E_le_M (x : ↥D.E).2⟩) * R := by
        rw [hR, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
        congr 2
        apply Subtype.ext
        have hx := D.mem_cE.mp x.2
        have h2 := congrArg Subtype.val hx
        change m * ((x : ↥D.E) : G) * m⁻¹ = ((x : ↥D.E) : G) at h2
        change m * ((x : ↥D.E) : G) = ((x : ↥D.E) : G) * m
        calc m * ((x : ↥D.E) : G) = m * ((x : ↥D.E) : G) * m⁻¹ * m := by group
          _ = _ := by rw [h2]
      rw [← rowsOf_mul, ← rowsOf_mul, hcomm]
    let f : ↥π.range → ↥((enumGrp Two.ebRows).filter fun e =>
        mulR (rowsOf R) e == mulR e (rowsOf R)).toFinset :=
      fun U => ⟨rowsOf (U : V12 ≃ₗ[ZMod 2] V12), List.mem_toFinset.mpr (hmemU U)⟩
    have hf : Function.Injective f := fun U V hUV =>
      Subtype.ext (rowsOf_injective (congrArg Subtype.val hUV))
    calc Nat.card π.range ≤ _ := Nat.card_le_card_of_injective f hf
      _ ≤ _ := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, Two.fixEb]
        exact List.toFinset_card_le _
  rw [h1, mul_comm]
  exact Nat.mul_le_mul hker hrange

end Bound

section Rstar

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

@[expose] noncomputable def Rstar : Subgroup ↥D.Mb := D.genC3 Two.r7Gens

include hOut hTw hHat

theorem Rstar_spec : ∀ φ ∈ D.Rstar, φ ∈ D.C3 ∧ D.kap (φ : MulAut ↥D.E) ∈ Two.enum7 Two.r7Gens := by
  obtain ⟨-, -, -, -, -, -, -, -, hid, hcl, -⟩ := Two.tOK48_spec
  exact (D.genC3_spec hOut hTw hHat Two.r7Gens_sub hid hcl).1

theorem Rstar_le_Cb : D.Rstar ≤ D.Cb := fun φ hφ => (D.Rstar_spec hOut hTw hHat φ hφ).1.2

theorem card_Rstar : Nat.card D.Rstar = 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, hid, hcl, h64, -⟩ := Two.tOK48_spec
  rw [Rstar, D.card_genC3 hOut hTw hHat Two.r7Gens_sub hid hcl, h64]

theorem isElemAbelian_Rstar : IsElemAbelian 2 D.Rstar := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcomm, hsq⟩ := Two.tOK48_spec
  have hz : ∀ φ ∈ D.Rstar, φ ∈ D.Mz := fun φ hφ => (D.Rstar_spec hOut hTw hHat φ hφ).1.1
  have hk : ∀ φ ∈ D.Rstar, D.kap (φ : MulAut ↥D.E) ∈ Two.enum7 Two.r7Gens := fun φ hφ =>
    (D.Rstar_spec hOut hTw hHat φ hφ).2
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · refine D.eq_of_kap_eq hOut hTw hHat (mul_mem (hz _ a.2) (hz _ b.2))
      (mul_mem (hz _ b.2) (hz _ a.2)) ?_
    simp only [Subgroup.coe_mul]
    rw [D.kap_mul (D.presE1_of_mem_Mz hOut hTw (hz _ a.2))
      (D.presE1_of_mem_Mz hOut hTw (hz _ b.2)), D.kap_mul (D.presE1_of_mem_Mz hOut hTw (hz _ b.2))
      (D.presE1_of_mem_Mz hOut hTw (hz _ a.2))]
    exact hcomm _ (hk _ a.2) _ (hk _ b.2)
  · rw [pow_two]
    refine D.eq_of_kap_eq hOut hTw hHat (mul_mem (hz _ hx) (hz _ hx)) (one_mem _) ?_
    simp only [Subgroup.coe_mul]
    rw [D.kap_mul (D.presE1_of_mem_Mz hOut hTw (hz _ hx))
      (D.presE1_of_mem_Mz hOut hTw (hz _ hx)), hsq _ (hk _ hx), Subgroup.coe_one, D.kap_one]

theorem ncard_conj_Rstar_le :
    {a : ↥D.Mb | a ∈ D.Rstar ∧ a ≠ 1 ∧ CFSG.Quasithin.A94.InZG D.tb a}.ncard ≤ 27 := by
  set S := {a : ↥D.Mb | a ∈ D.Rstar ∧ a ≠ 1 ∧ CFSG.Quasithin.A94.InZG D.tb a} with hS
  obtain ⟨-, -, hid, hc, -, -⟩ := Two.stabOK48_spec
  set L := (Two.enum7 Two.r7Gens).filter fun X => X != Two.id7 &&
    (enumGrp (Two.stabGens48 ())).any fun r => Two.res6 r == Two.aPart X &&
      decide (128 ≤ Two.fix7 X * Two.fixEb r) with hL
  have hmem : ∀ a ∈ S, D.kap (a : MulAut ↥D.E) ∈ L := by
    rintro a ⟨haR, ha1, g, hg⟩
    obtain ⟨haC, hak⟩ := D.Rstar_spec hOut hTw hHat a haR
    have haC' := haC
    rw [D.C3_eq_img hOut hTw hHat] at haC'
    obtain ⟨m, hmN, hmG, hma⟩ := D.mem_img.mp haC'
    have hm13 : m ∈ D.G13 := D.Ghat_le_G13 hmG
    have hmM : m ∈ h.setting.M := D.G13_le_M hm13
    have hS48 : D.Φo (h.setting.ρ ⟨m, hmM⟩) ∈ genGrp (Two.stabGens48 ()) :=
      rho_mem_of_mem_pre hmG hmM
    obtain ⟨r, hr, hUr⟩ := complete hid hc _ hS48
    have hrU := rowsOf_eq (enumGrp_sound Two.gensOK_stab48 r hr).1 hUr
    have hkap : D.kap (a : MulAut ↥D.E) = Two.mk7 (Two.lam6 (D.kap (a : MulAut ↥D.E))) (Two.res6 r) := by
      have := D.kap_toMb hOut hTw hm13
      rw [show D.toMb ⟨m, D.G13_le_N hm13⟩ = a from hma] at this
      rw [← hrU]
      exact this
    have hres : Two.res6 r ∈ Two.s48 () := by
      simp only [Two.s48, List.mem_dedup, List.mem_map]
      exact ⟨r, hr, rfl⟩
    have hA6 := (Two.c3OK48_spec.1 _ hres).1
    have hcard : 128 ≤ Two.fix7 (D.kap (a : MulAut ↥D.E)) * Two.fixEb r := by
      have h1 := D.card_cE_le hOut hTw hmN hmM (hma ▸ haC.1)
      rw [hma, hrU] at h1
      have h2 : Nat.card (D.cE a) = 128 := by
        have h3 := D.card_cE_conj (g⁻¹) D.tb
        rw [inv_inv] at h3
        rw [hg, h3, D.card_cE_tb hOut hTw hHat]
      rw [h2] at h1
      exact h1
    refine List.mem_filter.mpr ⟨hak, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    refine ⟨fun h1 => ha1 ?_, r, hr, ?_, hcard⟩
    · refine D.eq_of_kap_eq hOut hTw hHat haC.1 (one_mem _) ?_
      rw [h1, Subgroup.coe_one, D.kap_one]
    · rw [hkap, Two.aPart_mk7 hA6]
  have hinj : Set.InjOn (fun a : ↥D.Mb => D.kap (a : MulAut ↥D.E)) S := by
    intro a ha b hb hab
    exact D.eq_of_kap_eq hOut hTw hHat (D.Rstar_spec hOut hTw hHat a ha.1).1.1
      (D.Rstar_spec hOut hTw hHat b hb.1).1.1 hab
  calc S.ncard = ((fun a : ↥D.Mb => D.kap (a : MulAut ↥D.E)) '' S).ncard := (hinj.ncard_image).symm
    _ ≤ (↑L.toFinset : Set (Array ℕ)).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨a, ha, rfl⟩
        exact List.mem_toFinset.mpr (hmem a ha)
    _ = L.dedup.length := by rw [Set.ncard_coe_finset, List.card_toFinset]
    _ ≤ 27 := Two.fusOK48_spec

end Rstar

end Data41

end CFSG.Quasithin.H13.AS91
