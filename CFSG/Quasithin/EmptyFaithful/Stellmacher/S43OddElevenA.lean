module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCoreData
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddW
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Eleven

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h hb) a⁻¹).mp (A.inv_mem ha)
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact A.mul_mem ha h1

omit [Finite G] in
theorem commutator_le_right_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : ⁅A, B⁆ ≤ B := by
  rw [Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer h

omit [Finite G] in
theorem commutatorElement_mul_left (z q x : G) : ⁅z * q, x⁆ = z * ⁅q, x⁆ * z⁻¹ * ⁅z, x⁆ := by
  simp only [commutatorElement_def]; group

omit [Finite G] in
theorem conj_mem_centralizer {Y : Subgroup G} {g v : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hv : v ∈ Subgroup.centralizer (Y : Set G)) :
    g * v * g⁻¹ ∈ Subgroup.centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hv _ hy'
  calc y * (g * v * g⁻¹) = g * ((g⁻¹ * y * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = g * v * g⁻¹ * y := by group

omit [Finite G] in
theorem conj_mem_sup {A B N : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ N)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ N) {n : G} (hn : n ∈ A ⊔ B) : g * n * g⁻¹ ∈ N := by
  have key : A ⊔ B ≤ conjSub g⁻¹ N :=
    sup_le (fun a ha => mem_conjSub.mpr (by simpa using hA a ha))
      (fun b hb => mem_conjSub.mpr (by simpa using hB b hb))
  simpa using mem_conjSub.mp (key hn)

omit [Finite G] in
theorem conj_mem_commutator {A B N : Subgroup G} {g : G}
    (h : ∀ a ∈ A, ∀ b ∈ B, g * ⁅a, b⁆ * g⁻¹ ∈ N) {n : G} (hn : n ∈ ⁅A, B⁆) :
    g * n * g⁻¹ ∈ N := by
  have key : ⁅A, B⁆ ≤ conjSub g⁻¹ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact mem_conjSub.mpr (by simpa using h a ha b hb)
  simpa using mem_conjSub.mp (key hn)

theorem comm_mem_of_edge (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {α' ν : Geo H M} (hα' : vtype α' = true) (hν : ν ∈ nbrs α') {z : G}
    (hz : z ∈ stab ν ⊓ stab α') (hzQ : z ∉ Qv α')
    (hzC : z ∈ Subgroup.centralizer (Yv α' : Set G)) {u : G} (hu : u ∈ stab ν ⊓ stab α')
    (huC : u ∈ Subgroup.centralizer (Yv α' : Set G)) {x : G} (hx : x ∈ Vn α') :
    ⁅u, x⁆ ∈ ⁅Vn α', Subgroup.zpowers z⁆ ⊔ Yv α' := by
  have hνv : vtype ν = false := Sit43.vtype_false_of_adj hα' hν
  have h2 : (Qv α').relIndex (stab ν ⊓ stab α') = 2 :=
    Sit43.relIndex_Qv_edge hA hνv (nbrs_symm hν)
  have hY : ∀ q ∈ Qv α', q ∈ Subgroup.centralizer (Yv α' : Set G) → ⁅q, x⁆ ∈ Yv α' := by
    intro q hq hqC
    have h1 := Subgroup.commutator_mem_commutator hx (show q ∈ Qst α' from ⟨hq, hqC⟩)
    rw [hs.comm_Vn_Qst hA h26 hα' hν] at h1
    rw [← commutatorElement_inv]
    exact (Yv α').inv_mem h1
  by_cases huQ : u ∈ Qv α'
  · exact Subgroup.mem_sup_right (hY u huQ huC)
  · have hq : z⁻¹ * u ∈ Qv α' := inv_mul_mem_of_relIndex_two h2 hz hu hzQ huQ
    have hqC : z⁻¹ * u ∈ Subgroup.centralizer (Yv α' : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hzC) huC
    have e : u = z * (z⁻¹ * u) := by group
    rw [e, commutatorElement_mul_left]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hs.stab_le_normalizer_Yv hA h26 hα' hz.2) _).mp
        (hY _ hq hqC)
    · rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _
        (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers z))

section Crit

variable {α' ν β : Geo H M}

theorem comm_Vn_le_Vn_beta (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hβ : β ∈ nbrs α)
    (hdβ : dist β ν + 2 = bMin H M) : ⁅Vn β, Vn α'⁆ ≤ Vn β :=
  commutator_le_left_of_le_normalizer
    ((Core.Vn_le_stab_beta hA hs ho hc (Core.dist_beta_crit hA hc hν hβ hdβ)).trans
      (stab_le_normalizer_Vn β))

theorem comm_Vn_le_Vn_crit (hA : F53Amalgam H M S) (hs : Sit43 α)
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hβ : β ∈ nbrs α)
    (hdβ : dist β ν + 2 = bMin H M) : ⁅Vn β, Vn α'⁆ ≤ Vn α' :=
  commutator_le_right_of_le_normalizer
    ((Core.Vn_beta_le_stab hA hs hβ (Core.dist_beta_crit hA hc hν hβ hdβ)).trans
      (stab_le_normalizer_Vn α'))

theorem Qv_le_centralizer_Yv (hA : F53Amalgam H M S) (hν : ν ∈ nbrs α') :
    Qv ν ≤ Subgroup.centralizer (Yv α' : Set G) :=
  (Qv_le_centralizer_Zv hA ν).trans (Subgroup.centralizer_le (Yv_le_Zv hν))

theorem exists_z (hA : F53Amalgam H M S) (hs : Sit43 α) (hc : IsCritPair₁ α α')
    (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M) :
    ∃ z ∈ Zv α, z ∉ Qv α' ∧ z ∈ stab ν ⊓ stab α' ∧
      z ∈ Subgroup.centralizer (Yv α' : Set G) := by
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv α, z ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hc.1 fun x hx => hcon x hx
  exact ⟨z, hz, hzQ, Core.Zv_le_edge_nu hA hs hν hdν hz,
    Qv_le_centralizer_Yv hA hν (Core.Zv_le_Qv_nu hs hdν hz)⟩

omit [Finite G] in
theorem comm_zpowers_le {z : G} (hβ : β ∈ nbrs α) (hz : z ∈ Zv α) :
    ⁅Vn α', Subgroup.zpowers z⁆ ≤ ⁅Vn β, Vn α'⁆ := by
  rw [Subgroup.commutator_comm (Vn β)]
  exact Subgroup.commutator_mono le_rfl
    ((Subgroup.zpowers_le).mpr (Core.Zv_le_Vn (nbrs_symm hβ) hz))

theorem edge_le_normalizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) :
    stab ν ⊓ stab α' ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Zv ν : Subgroup G) : Set G) := by
  have hα'v : vtype α' = true := Core.vtype_crit hA hs ho hc
  obtain ⟨z, hz, hzQ, hzE, hzC⟩ := exists_z hA hs hc hν hdν
  have hVβ : Vn β ≤ Qv ν := Core.Vn_beta_le_Qv_nu hA hs hβ hdβ
  have hQνE : Qv ν ≤ stab ν ⊓ stab α' :=
    le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hν))
  have hsub : ⁅Vn α', Subgroup.zpowers z⁆ ⊔ Yv α' ≤ ⁅Vn β, Vn α'⁆ ⊔ Zv ν :=
    sup_le_sup (comm_zpowers_le hβ hz) (Yv_le_Zv hν)
  refine Sit43.le_normalizer_of_conj_mem fun g hg n hn => conj_mem_sup ?_ ?_ hn
  · intro r hr
    refine conj_mem_commutator (fun v hv x hx => ?_) hr
    have e : g * ⁅v, x⁆ * g⁻¹ = ⁅g * v * g⁻¹, g * x * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hvE : g * v * g⁻¹ ∈ stab ν ⊓ stab α' :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hQνE (hVβ hv))) (Subgroup.inv_mem _ hg)
    have hvC : g * v * g⁻¹ ∈ Subgroup.centralizer (Yv α' : Set G) :=
      conj_mem_centralizer (hs.stab_le_normalizer_Yv hA h26 hα'v hg.2)
        (Qv_le_centralizer_Yv hA hν (hVβ hv))
    have hxV : g * x * g⁻¹ ∈ Vn α' :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn α' hg.2) x).mp hx
    exact hsub (comm_mem_of_edge hA h26 hs hα'v hν hzE hzQ hzC hvE hvC hxV)
  · intro y hy
    exact Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA ν hg.1) y).mp hy)

theorem Wn_inf_stab_le_normalizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) :
    Wn α ⊓ stab ν ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Zv ν : Subgroup G) : Set G) := by
  have hW := isElemAbelian_Wn_of_five hA hs hb5
  have hRW : ⁅Vn β, Vn α'⁆ ≤ Wn α :=
    (comm_Vn_le_Vn_beta hA hs ho hc hν hβ hdβ).trans (hs.Vn_le_Wn hA h26 hβ)
  refine Sit43.le_normalizer_of_conj_mem fun w hw n hn => conj_mem_sup ?_ ?_ hn
  · intro r hr
    have hwr : w * r = r * w := isElemAbelian_comm hW hw.1 (hRW hr)
    have e : w * r * w⁻¹ = r := by rw [hwr]; group
    rw [e]
    exact Subgroup.mem_sup_left hr
  · intro y hy
    exact Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA ν hw.2) y).mp hy)

end Crit

end Eleven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
