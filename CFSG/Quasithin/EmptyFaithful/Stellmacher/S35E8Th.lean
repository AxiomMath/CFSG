module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChLat2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ : Geo H M}

open scoped Classical in
@[expose] noncomputable def th (c : Ch.Chart δ) (g : G) : Perm (Fin 5) :=
  if h : g ∈ stab δ then c.θ ⟨g, h⟩ else 1

open scoped Classical in
@[expose] noncomputable def pg (c : Ch.Chart δ) (x : G) : orth.W :=
  if h : x ∈ Vn δ then c.π ⟨x, h⟩ else 1

variable (c : Ch.Chart δ)

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
  rw [pg_of_mem c (Ch.conj_mem_Vn hg hx), pg_of_mem c hx, th_of_mem c hg]
  exact c.π_conj ⟨g, hg⟩ ⟨x, hx⟩

omit [Finite G] in
theorem pg_eq_iff {x y : G} (hx : x ∈ Vn δ) (hy : y ∈ Vn δ) :
    pg c x = pg c y ↔ x * y⁻¹ ∈ Zv δ := by
  rw [pg_of_mem c hx, pg_of_mem c hy]
  exact c.π_eq_iff ⟨x, hx⟩ ⟨y, hy⟩

omit [Finite G] in
theorem pg_surj (w : orth.W) : ∃ x, x ∈ Vn δ ∧ pg c x = w := by
  obtain ⟨x, rfl⟩ := c.π_surj w
  exact ⟨x, x.2, pg_of_mem c x.2⟩

omit [Finite G] in
theorem pg_eq_one_iff {x : G} (hx : x ∈ Vn δ) : pg c x = 1 ↔ x ∈ Zv δ := by
  rw [pg_of_mem c hx]
  exact c.π_eq_one ⟨x, hx⟩

omit [Finite G] in
theorem comm_iff {g x : G} (hg : g ∈ stab δ) (hx : x ∈ Vn δ) :
    g * x * g⁻¹ * x⁻¹ ∈ Zv δ ↔ orth.act (th c g) (pg c x) = pg c x := by
  rw [← pg_conj c hg hx, pg_eq_iff c (Ch.conj_mem_Vn hg hx) hx]

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

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
