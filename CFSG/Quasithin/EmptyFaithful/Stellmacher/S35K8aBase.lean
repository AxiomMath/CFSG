module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.K8a

open S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ : Geo H M}

open scoped Classical in
@[expose] noncomputable def th (c : Chart2 δ) (g : G) : Perm (Fin 5) :=
  if h : g ∈ stab δ then c.θ ⟨g, h⟩ else 1

open scoped Classical in
@[expose] noncomputable def pg (c : Chart2 δ) (x : G) : orth.W :=
  if h : x ∈ Vn δ then c.π ⟨x, h⟩ else 1

variable (c : Chart2 δ)

omit [Finite G] in
theorem th_of_mem {g : G} (hg : g ∈ stab δ) : th c g = c.θ ⟨g, hg⟩ := by
  simp [th, hg]

omit [Finite G] in
theorem pg_of_mem {x : G} (hx : x ∈ Vn δ) : pg c x = c.π ⟨x, hx⟩ := by
  simp [pg, hx]

omit [Finite G] in
theorem th_mul {g h : G} (hg : g ∈ stab δ) (hh : h ∈ stab δ) :
    th c (g * h) = th c g * th c h := by
  rw [th_of_mem c hg, th_of_mem c hh, th_of_mem c ((stab δ).mul_mem hg hh)]
  exact map_mul c.θ ⟨g, hg⟩ ⟨h, hh⟩

omit [Finite G] in
theorem th_one : th c (1 : G) = 1 := by
  rw [th_of_mem c (stab δ).one_mem]
  exact map_one c.θ

omit [Finite G] in
theorem th_inv {g : G} (hg : g ∈ stab δ) : th c g⁻¹ = (th c g)⁻¹ := by
  rw [th_of_mem c ((stab δ).inv_mem hg), th_of_mem c hg]
  exact map_inv c.θ ⟨g, hg⟩

omit [Finite G] in
theorem pg_mul {x y : G} (hx : x ∈ Vn δ) (hy : y ∈ Vn δ) :
    pg c (x * y) = pg c x * pg c y := by
  rw [pg_of_mem c hx, pg_of_mem c hy, pg_of_mem c ((Vn δ).mul_mem hx hy)]
  exact map_mul c.π ⟨x, hx⟩ ⟨y, hy⟩

omit [Finite G] in
theorem pg_inv {x : G} (hx : x ∈ Vn δ) : pg c x⁻¹ = (pg c x)⁻¹ := by
  rw [pg_of_mem c ((Vn δ).inv_mem hx), pg_of_mem c hx]
  exact map_inv c.π ⟨x, hx⟩

omit [Finite G] in
theorem pg_conj {g x : G} (hg : g ∈ stab δ) (hx : x ∈ Vn δ) :
    pg c (g * x * g⁻¹) = orth.act (th c g) (pg c x) := by
  rw [pg_of_mem c (S35.Ch.conj_mem_Vn hg hx), pg_of_mem c hx, th_of_mem c hg]
  exact c.π_conj ⟨g, hg⟩ ⟨x, hx⟩

omit [Finite G] in
theorem pg_eq_iff {x y : G} (hx : x ∈ Vn δ) (hy : y ∈ Vn δ) :
    pg c x = pg c y ↔ x * y⁻¹ ∈ Cb δ := by
  rw [pg_of_mem c hx, pg_of_mem c hy]
  exact c.π_eq_iff ⟨x, hx⟩ ⟨y, hy⟩

omit [Finite G] in
theorem pg_surj (w : orth.W) : ∃ x, x ∈ Vn δ ∧ pg c x = w := by
  obtain ⟨x, rfl⟩ := c.π_surj w
  exact ⟨x, x.2, pg_of_mem c x.2⟩

omit [Finite G] in
theorem pg_eq_one_iff {x : G} (hx : x ∈ Vn δ) : pg c x = 1 ↔ x ∈ Cb δ := by
  rw [pg_of_mem c hx]
  exact c.π_eq_one ⟨x, hx⟩

omit [Finite G] in
theorem comm_Cb_iff {g x : G} (hg : g ∈ stab δ) (hx : x ∈ Vn δ) :
    g * x * g⁻¹ * x⁻¹ ∈ Cb δ ↔ orth.act (th c g) (pg c x) = pg c x := by
  rw [← pg_conj c hg hx, pg_eq_iff c (S35.Ch.conj_mem_Vn hg hx) hx]

omit [Finite G] in
theorem mem_pre_iff' {Y : Subgroup orth.W} {x : G} :
    x ∈ c.pre Y ↔ x ∈ Vn δ ∧ pg c x ∈ Y := by
  constructor
  · intro h
    have hx : x ∈ Vn δ := c.pre_le_Vn Y h
    exact ⟨hx, by rw [pg_of_mem c hx]; exact (c.mem_pre_iff ⟨x, hx⟩).mp h⟩
  · rintro ⟨hx, h⟩
    rw [pg_of_mem c hx] at h
    exact (c.mem_pre_iff ⟨x, hx⟩).mpr h

theorem th_eq_one_iff (hS : Sit H M S) (hδ : vtype δ = false) {g : G} (hg : g ∈ stab δ) :
    th c g = 1 ↔ g ∈ Qv δ := by
  rw [th_of_mem c hg]
  exact c.ker_iff hS hδ ⟨g, hg⟩

include c in
omit [Finite G] in
theorem stab_le_normalizer_Cb : stab δ ≤ Subgroup.normalizer (Cb δ : Set G) := by
  have key : ∀ g ∈ stab δ, ∀ z ∈ Cb δ, g * z * g⁻¹ ∈ Cb δ := by
    intro g hg z hz
    have hzV : z ∈ Vn δ := c.le hz
    have h1 : pg c (g * z * g⁻¹) = 1 := by
      rw [pg_conj c hg hzV, (pg_eq_one_iff c hzV).mpr hz, map_one]
    exact (pg_eq_one_iff c (S35.Ch.conj_mem_Vn hg hzV)).mp h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ ((stab δ).inv_mem hg) _ hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

include c in
theorem comm_Zv_of_comm_Cb (hS : Sit H M S) (hδ : vtype δ = false) (hRk : S35.II.RkZvEq H M)
    {g x : G} (hg : g ∈ stab δ) (hx : x ∈ Vn δ) (h : g * x * g⁻¹ * x⁻¹ ∈ Cb δ) :
    g * x * g⁻¹ * x⁻¹ ∈ Zv δ := by
  have hZV : Vn δ ≤ Subgroup.normalizer (Zv δ : Set G) :=
    ((Std.Vn_le_Qv_self hS δ).trans (S35.Ch.Qv_le_stab' δ)).trans
      (stab_le_normalizer_Zv hS.glob.amalg δ)
  have hgZ : g ∈ Subgroup.normalizer (Zv δ : Set G) := stab_le_normalizer_Zv hS.glob.amalg δ hg
  have hVC : Vn δ ≤ Subgroup.normalizer (Cb δ : Set G) := c.Vn_le_normalizer_Cb
  have hgC : g ∈ Subgroup.normalizer (Cb δ : Set G) := stab_le_normalizer_Cb c hg
  have hZC : Zv δ ≤ Cb δ := S34.Zv_le_Cb hS.glob hδ
  have hle : fixSecIn (Subgroup.zpowers g) (Zv δ) (Vn δ) ≤
      fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ) := by
    intro z hz
    rw [mem_fixSecIn_zpowers_iff hZV hgZ] at hz
    rw [mem_fixSecIn_zpowers_iff hVC hgC]
    exact ⟨hz.1, hZC hz.2⟩
  have hidx := hRk δ hδ g hg
  unfold S34.rk secIdx at hidx
  have hmul := Subgroup.relIndex_mul_relIndex _ _ (Vn δ) hle
    (S35.Ch2.Chart2.fixSecIn_le_Vn (δ := δ) _)
  have hne : (fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ)).relIndex (Vn δ) ≠ 0 :=
    by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite
  have h1 : (fixSecIn (Subgroup.zpowers g) (Zv δ) (Vn δ)).relIndex
      (fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ)) = 1 := by
    rw [hidx] at hmul
    have : (fixSecIn (Subgroup.zpowers g) (Zv δ) (Vn δ)).relIndex
        (fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ)) *
        (fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ)).relIndex (Vn δ) =
        1 * (fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ)).relIndex (Vn δ) := by
      rw [hmul, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  have h2 := Subgroup.relIndex_eq_one.mp h1
  have hx' : x ∈ fixSecIn (Subgroup.zpowers g) (Cb δ) (Vn δ) := by
    rw [mem_fixSecIn_zpowers_iff hVC hgC]
    exact ⟨hx, h⟩
  have := h2 hx'
  rw [mem_fixSecIn_zpowers_iff hZV hgZ] at this
  exact this.2

theorem comm_iff (hS : Sit H M S) (hδ : vtype δ = false) (hRk : S35.II.RkZvEq H M)
    {g x : G} (hg : g ∈ stab δ) (hx : x ∈ Vn δ) :
    g * x * g⁻¹ * x⁻¹ ∈ Zv δ ↔ orth.act (th c g) (pg c x) = pg c x := by
  rw [← comm_Cb_iff c hg hx]
  exact ⟨fun h => S34.Zv_le_Cb hS.glob hδ h, comm_Zv_of_comm_Cb c hS hδ hRk hg hx⟩

end S35.K8a

end F53.Stellmacher

end CFSG.Quasithin
