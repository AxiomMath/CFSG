module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaIBase
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaIAux

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

omit C in
theorem stab_le_normalizer_Cv' (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) := fun _ hg =>
  mem_normalizer_inf' (stab_le_normalizer_Vn δ hg)
    (mem_normalizer_centralizer' (le_normalizer_oTwoRes (stab δ) hg))

theorem Iv_inf_Cv_le_Qv {ν δ : Geo H M} (hδ : δ ∈ nbrs ν) (hvδ : vtype δ = false) :
    Iv ν ⊓ F53B3.Cv δ ≤ Qv δ :=
  inf_le_left.trans ((Iv_le_Vn hδ).trans (C.Vn_le_Qv_self hvδ))

theorem Iv_inf_Cv_inf_centralizer_eq_bot {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    {d : ↥(H ⊔ M)} (hdst : (d : G) ∈ stab ν) (hd3 : (d : G) ^ 3 = 1) (hdQ : (d : G) ∉ Qv ν) :
    Iv ν ⊓ F53B3.Cv δ ⊓ Subgroup.centralizer ({(d : G)} : Set G) = ⊥ := by
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  have hνδ : ν ∈ nbrs δ := mem_nbrs_comm hδ
  refine eq_bot_of_normalizer_transitive_vertex C.hA hνδ (U := Iv ν ⊓ F53B3.Cv δ ⊓
    Subgroup.centralizer ({(d : G)} : Set G)) ?_ ?_ ?_
  · intro x hx
    exact Qv_le_inf C.hA hνδ (C.Iv_inf_Cv_le_Qv hδ hvδ hx.1)
  · intro ε hε ε' hε'
    obtain ⟨x, hxL, hxε⟩ := C.exists_oTwoRes_smul hε hε'
    refine ⟨x, mem_normalizer_of_commute fun z hz => ?_, smul_eq_of_mem_stab (oTwoRes_le _ hxL),
      hxε⟩
    exact (Subgroup.mem_centralizer_iff.mp hz.1.2.2) x hxL
  · intro ε hε ε' hε'
    obtain ⟨i, hi⟩ := C.cube_exists_pow_smul hν hε hε' hdst hd3 hdQ
    have hxe : ((d ^ i : ↥(H ⊔ M)) : G) = (d : G) ^ i := rfl
    have hxst : ((d ^ i : ↥(H ⊔ M)) : G) ∈ stab ν := by rw [hxe]; exact pow_mem hdst i
    refine ⟨d ^ i, mem_normalizer_of_commute fun z hz => ?_, smul_eq_of_mem_stab hxst, hi⟩
    have hc : Commute z (d : G) := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    rw [hxe]
    exact ((hc.pow_right i).symm).eq

theorem card_Iv_inf_Cv_le {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν) :
    Nat.card ↥(Iv ν ⊓ F53B3.Cv δ) ≤ 4 := by
  obtain ⟨d, hdst, hd3, hdQ⟩ := C.exists_cube hν
  have hX := C.Iv_inf_Cv_inf_centralizer_eq_bot hν hδ (d := ⟨d, stab_le ν hdst⟩) hdst hd3 hdQ
  have hdK : d ∈ Kd ν := C.cube_mem_Kd hν hδ hdst hd3
  let f : ↥(Iv ν ⊓ F53B3.Cv δ) → ↥(Zv ν) := fun x => ⟨⁅(x : G), d⁆, hdK.2.2 x x.2.1⟩
  have hinj : Function.Injective f := by
    intro x x' h
    have h1 : ⁅(x : G), d⁆ = ⁅(x' : G), d⁆ := congrArg Subtype.val h
    have h' : (x : G) * d * (x : G)⁻¹ = (x' : G) * d * (x' : G)⁻¹ := by
      simp only [commutatorElement_def] at h1
      exact mul_right_cancel h1
    have hz : (x' : G)⁻¹ * x ∈ Iv ν ⊓ F53B3.Cv δ ⊓ Subgroup.centralizer ({d} : Set G) := by
      refine ⟨(Iv ν ⊓ F53B3.Cv δ).mul_mem ((Iv ν ⊓ F53B3.Cv δ).inv_mem x'.2) x.2,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (x' : G)⁻¹ * x * d = (x' : G)⁻¹ * ((x : G) * d * (x : G)⁻¹) * x := by group
        _ = (x' : G)⁻¹ * ((x' : G) * d * (x' : G)⁻¹) * x := by rw [h']
        _ = d * ((x' : G)⁻¹ * x) := by group
    rw [hX, Subgroup.mem_bot] at hz
    exact Subtype.ext (inv_mul_eq_one.mp hz).symm
  have := Nat.card_le_card_of_injective f hinj
  rwa [C.card_Zv_true hν] at this

theorem Iv_inf_Cv_inf_Zv {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν) :
    Iv ν ⊓ F53B3.Cv δ ⊓ Zv ν = Zv δ := by
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  apply le_antisymm
  · intro x hx
    have : x ∈ Zv ν ⊓ F53B3.Cv δ := ⟨hx.2, hx.1.2⟩
    rwa [C.Zv_inf_Cv_eq hvδ (mem_nbrs_comm hδ)] at this
  · exact le_inf (le_inf ((C.Zv_le_Zv_of_mem_nbrs hν hδ).trans C.Zv_le_Iv) (C.Zv_le_Cv hvδ))
      (C.Zv_le_Zv_of_mem_nbrs hν hδ)

theorem Qv_centralizes_Zv {ν : Geo H M} (hν : vtype ν = true) {q z : G} (hq : q ∈ Qv ν)
    (hz : z ∈ Zv ν) : q * z * q⁻¹ = z := by
  have h := centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hν)
  rw [← h] at hq
  have := Subgroup.mem_centralizer_iff.mp hq.2 z hz
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem comm_Qv_mem_Zv {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2) {y q : G}
    (hy : y ∈ Iv ν ⊓ F53B3.Cv δ) (hq : q ∈ Qv ν) : y⁻¹ * q * y * q⁻¹ ∈ Zv δ := by
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  have hqs : q ∈ stab ν ⊓ stab δ := Qv_le_inf C.hA hδ hq
  have hqz := fun z hz => C.Qv_centralizes_Zv hν hq (z := z) hz
  have hqy : q * y * q⁻¹ ∈ Iv ν ⊓ F53B3.Cv δ := by
    have hN := mem_normalizer_inf' (stab_le_normalizer_Iv ν hqs.1)
      (stab_le_normalizer_Cv' δ hqs.2)
    exact (Subgroup.mem_normalizer_iff.mp hN y).mp hy
  by_cases hyZ : y ∈ Zv ν
  · have h1 := hqz y hyZ
    have : y⁻¹ * q * y * q⁻¹ = 1 := by
      calc y⁻¹ * q * y * q⁻¹ = y⁻¹ * (q * y * q⁻¹) := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    exact one_mem _
  · have hyZδ : y ∉ Zv δ := fun h => hyZ (C.Zv_le_Zv_of_mem_nbrs hν hδ h)
    have hwZδ : q * y * q⁻¹ ∉ Zv δ := by
      intro h
      have h1 := hqz _ (C.Zv_le_Zv_of_mem_nbrs hν hδ h)
      have h2 : y = q * y * q⁻¹ := by
        calc y = q⁻¹ * (q * y * q⁻¹) * q := by group
          _ = q⁻¹ * (q * (q * y * q⁻¹) * q⁻¹) * q := by rw [h1]
          _ = q * y * q⁻¹ := by group
      exact hyZδ (h2 ▸ h)
    have := inv_mul_mem_of_relIndex_two hrel hy hqy hyZδ hwZδ
    have e : y⁻¹ * q * y * q⁻¹ = y⁻¹ * (q * y * q⁻¹) := by group
    rw [e]
    exact this

theorem comm_stab_mem_Zv {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2) {y g : G}
    (hy : y ∈ Iv ν ⊓ F53B3.Cv δ) (hg : g ∈ stab ν) : y⁻¹ * g * y * g⁻¹ ∈ Zv ν := by
  have hQN : Qv ν ≤ Subgroup.normalizer (Kd ν : Set G) :=
    (pCoreOf_le 2 (stab ν)).trans (C.stab_le_normalizer_Kd ν)
  obtain ⟨k, hk, q, hq, rfl⟩ := mem_sup_of_le_normalizer hQN (C.stab_le_Kd_sup hν hδ hg)
  have hz₁ := C.comm_Qv_mem_Zv hν hδ hrel hy hq
  have hz₂ : y⁻¹ * k * y * k⁻¹ ∈ Zv ν := by
    have := hk.2.2 y⁻¹ (Subgroup.inv_mem _ hy.1)
    simpa [commutatorElement_def] using this
  have hz₁' : k * (y⁻¹ * q * y * q⁻¹) * k⁻¹ ∈ Zv ν :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA ν hk.1) _).mp
      (C.Zv_le_Zv_of_mem_nbrs hν hδ hz₁)
  have e : y⁻¹ * (k * q) * y * (k * q)⁻¹ =
      (y⁻¹ * k * y * k⁻¹) * (k * (y⁻¹ * q * y * q⁻¹) * k⁻¹) := by group
  rw [e]
  exact (Zv ν).mul_mem hz₂ hz₁'

theorem Qv_centralizes_J {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2) {y q : G}
    (hy : y ∈ Iv ν ⊓ F53B3.Cv δ) (hq : q ∈ Qv ν) : y⁻¹ * q * y * q⁻¹ = 1 := by
  obtain ⟨μ, hμ, hδμ⟩ := exists_mem_nbrs_ne C.hA ν hδ
  obtain ⟨g, hgst, hgδ⟩ := stab_transitive_on_nbrs hδ hμ
  have hcZ : y⁻¹ * q * y * q⁻¹ ∈ Zv δ := C.comm_Qv_mem_Zv hν hδ hrel hy hq
  have hgq : (g : G) * q * (g : G)⁻¹ ∈ Qv ν :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab ν) hgst) q).mp hq
  have hc' := C.comm_Qv_mem_Zv hν hδ hrel hy hgq
  have hz : y⁻¹ * ((g : G)⁻¹ * y * (g : G)) ∈ Zv ν := by
    have := C.comm_stab_mem_Zv hν hδ hrel hy (Subgroup.inv_mem _ hgst)
    simpa [mul_assoc] using this
  have hcomm : ∀ a ∈ Zv ν, ∀ b ∈ Zv ν, a * b = b * a :=
    isMulCommutative_subgroup_iff.mp (isElemAbelian_Zv C.hA ν).1
  have hcν : y⁻¹ * q * y * q⁻¹ ∈ Zv ν := C.Zv_le_Zv_of_mem_nbrs hν hδ hcZ
  obtain ⟨z, hzdef⟩ : ∃ z, z = y⁻¹ * ((g : G)⁻¹ * y * (g : G)) := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have e1 : (g : G)⁻¹ * y * (g : G) = y * z := by rw [hzdef]; group
  have hqz := C.Qv_centralizes_Zv hν hq hz
  have hzc : z⁻¹ * (y⁻¹ * q * y * q⁻¹) * z = y⁻¹ * q * y * q⁻¹ := by
    have h1 := hcomm _ hcν z hz
    calc z⁻¹ * (y⁻¹ * q * y * q⁻¹) * z = z⁻¹ * ((y⁻¹ * q * y * q⁻¹) * z) := by group
      _ = z⁻¹ * (z * (y⁻¹ * q * y * q⁻¹)) := by rw [h1]
      _ = y⁻¹ * q * y * q⁻¹ := by group
  have key : y⁻¹ * ((g : G) * q * (g : G)⁻¹) * y * ((g : G) * q * (g : G)⁻¹)⁻¹ =
      (g : G) * (y⁻¹ * q * y * q⁻¹) * (g : G)⁻¹ := by
    calc y⁻¹ * ((g : G) * q * (g : G)⁻¹) * y * ((g : G) * q * (g : G)⁻¹)⁻¹
        = (g : G) * (((g : G)⁻¹ * y * (g : G))⁻¹ * q * ((g : G)⁻¹ * y * (g : G)) * q⁻¹) *
            (g : G)⁻¹ := by group
      _ = (g : G) * ((y * z)⁻¹ * q * (y * z) * q⁻¹) * (g : G)⁻¹ := by rw [e1]
      _ = (g : G) * (z⁻¹ * (y⁻¹ * q * y * q⁻¹) * (q * z * q⁻¹)) * (g : G)⁻¹ := by group
      _ = (g : G) * (z⁻¹ * (y⁻¹ * q * y * q⁻¹) * z) * (g : G)⁻¹ := by rw [hqz]
      _ = (g : G) * (y⁻¹ * q * y * q⁻¹) * (g : G)⁻¹ := by rw [hzc]
  rw [key] at hc'
  have hgμ : (g : G) * (y⁻¹ * q * y * q⁻¹) * (g : G)⁻¹ ∈ Zv μ := by
    have h1 : (g : G) * (y⁻¹ * q * y * q⁻¹) * (g : G)⁻¹ ∈ Zv (g • δ) := by
      rw [Zv_smul]; exact mul_mem_conjSub hcZ
    rwa [hgδ] at h1
  have hinf := (C.Zv_sup_eq_and_inf_eq_bot hν hδ hμ hδμ.symm).2
  have hbot : (g : G) * (y⁻¹ * q * y * q⁻¹) * (g : G)⁻¹ ∈ (Zv δ ⊓ Zv μ) := ⟨hc', hgμ⟩
  rw [hinf, Subgroup.mem_bot] at hbot
  calc y⁻¹ * q * y * q⁻¹ = (g : G)⁻¹ * ((g : G) * (y⁻¹ * q * y * q⁻¹) * (g : G)⁻¹) * (g : G) := by
        group
    _ = 1 := by rw [hbot]; group

theorem Qv_comm_J {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2) {y q : G}
    (hy : y ∈ Iv ν ⊓ F53B3.Cv δ) (hq : q ∈ Qv ν) : q * y * q⁻¹ = y := by
  have h := C.Qv_centralizes_J hν hδ hrel hy hq
  calc q * y * q⁻¹ = y * (y⁻¹ * q * y * q⁻¹) := by group
    _ = y := by rw [h]; group

theorem stab_le_normalizer_K {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2) :
    stab ν ≤ Subgroup.normalizer ((Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ) : Subgroup G) : Set G) := by
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  have hJN : Iv ν ⊓ F53B3.Cv δ ≤ Subgroup.normalizer (Zv ν : Set G) := fun x hx =>
    stab_le_normalizer_Zv C.hA ν
      ((Qv_le_inf C.hA (mem_nbrs_comm hδ) (C.Iv_inf_Cv_le_Qv hδ hvδ hx)).2)
  have key : ∀ g ∈ stab ν, ∀ x ∈ Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ),
      g * x * g⁻¹ ∈ Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ) := by
    intro g hg x hx
    obtain ⟨n, hn, j, hj, rfl⟩ := mem_sup_of_le_normalizer hJN hx
    have h1 : g * n * g⁻¹ ∈ Zv ν :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA ν hg) n).mp hn
    have h2 := C.comm_stab_mem_Zv hν hδ hrel hj hg
    have e : g * (n * j) * g⁻¹ = (g * n * g⁻¹) * (j * (j⁻¹ * g * j * g⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right hj) (Subgroup.mem_sup_left h2))
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem card_K {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν)
    (hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2) :
    Nat.card ↥(Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ)) = 8 := by
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  have hJN : Iv ν ⊓ F53B3.Cv δ ≤ Subgroup.normalizer (Zv ν : Set G) := fun x hx =>
    stab_le_normalizer_Zv C.hA ν
      ((Qv_le_inf C.hA (mem_nbrs_comm hδ) (C.Iv_inf_Cv_le_Qv hδ hvδ hx)).2)
  have h1 := relIndex_sup_eq_relIndex_inf_right hJN
  have hZ : Zv ν ⊓ (Iv ν ⊓ F53B3.Cv δ) = Zv δ := by
    rw [inf_comm, C.Iv_inf_Cv_inf_Zv hν hδ]
  rw [hZ, hrel] at h1
  have h2 := Subgroup.relIndex_mul_card (H := Zv ν) (K := Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ))
  rw [inf_of_le_left (le_sup_left : Zv ν ≤ Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ)), h1, C.card_Zv_true hν] at h2
  omega

theorem false_of_Qv_centralizes {ν : Geo H M} (hν : vtype ν = true) {K : Subgroup G}
    (hKel : IsElemAbelian 2 K) (hK8 : Nat.card K = 8) (hZK : Zv ν ≤ K) (hKst : K ≤ stab ν)
    (hKN : stab ν ≤ Subgroup.normalizer (K : Set G))
    (hQK : ∀ q ∈ Qv ν, ∀ x ∈ K, q * x * q⁻¹ = x) : False := by
  obtain ⟨d, hdst, hd3, hdQ⟩ := C.exists_cube hν
  obtain ⟨k, hkK, hk1, hkd, hkuniq⟩ := exists_unique_fixed_of_card_eight hKel hK8
    hZK (C.card_Zv_true hν) (hKN hdst) hd3
    (C.cube_fixed_Zv hν hdst hd3 hdQ)
  obtain ⟨ψ, hs, hker⟩ := exists_quotHom_true C.hA hν
  have hkst : k ∈ stab ν := hKst hkK
  have hcen : ∀ g ∈ stab ν, g * k * g⁻¹ = k := by
    intro g hg
    obtain ⟨x, hxdef⟩ : ∃ x, x = g * k * g⁻¹ := ⟨_, rfl⟩
    have hxK : x ∈ K := by
      rw [hxdef]; exact (Subgroup.mem_normalizer_iff.mp (hKN hg) k).mp hkK
    have hx1 : x ≠ 1 := by
      intro h
      apply hk1
      calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
        _ = 1 := by rw [← hxdef, h]; group
    have e1 : (g * d * g⁻¹) * x * (g * d * g⁻¹)⁻¹ = x := by
      rw [hxdef]
      calc (g * d * g⁻¹) * (g * k * g⁻¹) * (g * d * g⁻¹)⁻¹ = g * (d * k * d⁻¹) * g⁻¹ := by group
        _ = g * k * g⁻¹ := by rw [hkd]
    have hfix : d * x * d⁻¹ = x := by
      have h3 : ψ ⟨d, hdst⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨d, hdst⟩ : ↥(stab ν)) ^ 3 = 1 := Subtype.ext hd3
        rw [this, map_one]
      have h1 : ψ ⟨d, hdst⟩ ≠ 1 := fun h => hdQ ((hker _).mp h)
      rcases perm3_conj_cube (ψ ⟨d, hdst⟩) (ψ ⟨g, hg⟩) h1 h3 with h | h
      · have hq : d⁻¹ * (g * d * g⁻¹) ∈ Qv ν := by
          have : ψ ((⟨d, hdst⟩ : ↥(stab ν))⁻¹ * (⟨g, hg⟩ * ⟨d, hdst⟩ * ⟨g, hg⟩⁻¹)) = 1 := by
            rw [map_mul, map_inv, map_mul, map_mul, map_inv, h]
            group
          simpa using (hker _).mp this
        have e2 : g * d * g⁻¹ = d * (d⁻¹ * (g * d * g⁻¹)) := by group
        calc d * x * d⁻¹ = d * ((d⁻¹ * (g * d * g⁻¹)) * x * (d⁻¹ * (g * d * g⁻¹))⁻¹) * d⁻¹ := by
              rw [hQK _ hq x hxK]
          _ = (d * (d⁻¹ * (g * d * g⁻¹))) * x * (d * (d⁻¹ * (g * d * g⁻¹)))⁻¹ := by group
          _ = (g * d * g⁻¹) * x * (g * d * g⁻¹)⁻¹ := by rw [← e2]
          _ = x := e1
      · have hq : d * (g * d * g⁻¹) ∈ Qv ν := by
          have : ψ ((⟨d, hdst⟩ : ↥(stab ν)) * (⟨g, hg⟩ * ⟨d, hdst⟩ * ⟨g, hg⟩⁻¹)) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, h]
            group
          simpa using (hker _).mp this
        have e2 : g * d * g⁻¹ = d⁻¹ * (d * (g * d * g⁻¹)) := by group
        have hinv : d⁻¹ * x * d = x := by
          calc d⁻¹ * x * d = d⁻¹ * ((d * (g * d * g⁻¹)) * x * (d * (g * d * g⁻¹))⁻¹) * d := by
                rw [hQK _ hq x hxK]
            _ = (d⁻¹ * (d * (g * d * g⁻¹))) * x * (d⁻¹ * (d * (g * d * g⁻¹)))⁻¹ := by group
            _ = (g * d * g⁻¹) * x * (g * d * g⁻¹)⁻¹ := by rw [← e2]
            _ = x := e1
        calc d * x * d⁻¹ = d * (d⁻¹ * x * d) * d⁻¹ := by rw [hinv]
          _ = x := by group
    rcases hkuniq x hxK hfix with h | h
    · exact absurd h hx1
    · rw [← hxdef]; exact h
  have hkc : k ∈ centerOf (stab ν) :=
    ⟨hkst, Subgroup.mem_centralizer_iff.mpr fun g hg => mul_inv_eq_iff_eq_mul.mp (hcen g hg)⟩
  rw [C.centerOf_eq_bot hν] at hkc
  exact hk1 (Subgroup.mem_bot.mp hkc)


theorem Iv_inf_Cv_eq {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν) :
    Iv ν ⊓ F53B3.Cv δ = Zv δ := by
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  have hZJ : Zv δ ≤ Iv ν ⊓ F53B3.Cv δ :=
    le_inf ((C.Zv_le_Zv_of_mem_nbrs hν hδ).trans C.Zv_le_Iv) (C.Zv_le_Cv hvδ)
  by_contra hne
  have hlt : Zv δ ≠ Iv ν ⊓ F53B3.Cv δ := fun h => hne h.symm
  have hle4 := C.card_Iv_inf_Cv_le hν hδ
  have hc2 := C.card_Zv_false hvδ
  have hdvd := Subgroup.card_dvd_of_le hZJ
  have hpos : 0 < Nat.card ↥(Iv ν ⊓ F53B3.Cv δ) := Nat.card_pos
  have hc4 : Nat.card ↥(Iv ν ⊓ F53B3.Cv δ) = 4 := by
    obtain ⟨m, hm⟩ := hdvd
    rw [hc2] at hm
    have : m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZJ (by omega)) hlt
    · omega
  have hrel : (Zv δ).relIndex (Iv ν ⊓ F53B3.Cv δ) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Zv δ) (K := Iv ν ⊓ F53B3.Cv δ)
    rw [inf_of_le_left hZJ, hc2, hc4] at h
    omega
  have hJN : Iv ν ⊓ F53B3.Cv δ ≤ Subgroup.normalizer (Zv ν : Set G) := fun x hx =>
    stab_le_normalizer_Zv C.hA ν
      ((Qv_le_inf C.hA (mem_nbrs_comm hδ) (C.Iv_inf_Cv_le_Qv hδ hvδ hx)).2)
  have hKI : Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ) ≤ Iv ν := sup_le C.Zv_le_Iv inf_le_left
  have hKel : IsElemAbelian 2 (Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ)) :=
    isElemAbelian_mono' hKI (C.isElemAbelian_Iv hδ)
  have hK8 := C.card_K hν hδ hrel
  have hKN := C.stab_le_normalizer_K hν hδ hrel
  have hKst : Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ) ≤ stab ν := fun x hx =>
    (Qv_le_inf C.hA (mem_nbrs_comm hδ)
      (C.Vn_le_Qv_self hvδ (Iv_le_Vn hδ (hKI hx)))).2
  have hQK : ∀ q ∈ Qv ν, ∀ x ∈ Zv ν ⊔ (Iv ν ⊓ F53B3.Cv δ), q * x * q⁻¹ = x := by
    intro q hq x hx
    obtain ⟨n, hn, j, hj, rfl⟩ := mem_sup_of_le_normalizer hJN hx
    calc q * (n * j) * q⁻¹ = (q * n * q⁻¹) * (q * j * q⁻¹) := by group
      _ = n * j := by rw [C.Qv_centralizes_Zv hν hq hn, C.Qv_comm_J hν hδ hrel hj hq]
  exact C.false_of_Qv_centralizes hν hKel hK8 le_sup_left hKst hKN hQK

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
