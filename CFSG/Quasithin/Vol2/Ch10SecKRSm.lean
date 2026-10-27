module

public import CFSG.Quasithin.Vol2.Ch10SecB5Three
public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.Tw_eq_T1_of_case3 (c : Conf T L I t w J) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3 : Case10_1_1Three T L I) (hcv : fsuCVM T L I = ⊥) :
    T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L := by
  refine le_antisymm (c.Tw_le_T1 h37 h38) fun s hs => ⟨hs.1, ?_⟩
  have h := c.claim.2.2.2.2.2 h3 s hs
  rw [hcv, Subgroup.mem_bot, mul_inv_eq_one] at h
  show s ∈ Subgroup.centralizer ({w} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc s * w = s * w * s⁻¹ * s := by group
    _ = w * s := by rw [h]

omit [Finite G] in
theorem conj_mem_centralizer {a x g : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
    _ = g * (a * x) * g⁻¹ := by rw [hx]
    _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group

variable (c : Conf T L I t w J) (hTw : T ⊓ Subgroup.centralizer ({w} : Set G) = T1 T L)
include c hTw

theorem Conf.t_mem_normalizer_Tw (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) :
    t ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) := by
  rw [hTw]
  exact SecB.T1_normal h37 h38 c.hyp c.ht

theorem Conf.t_sq_mem (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    t * t ∈ T ⊓ Subgroup.centralizer ({w} : Set G) := by
  rw [hTw]
  exact ⟨T.mul_mem c.ht c.ht, SecA.mul_self_mem_normalizer h37 h38 c.hyp c.ht c.htn⟩

theorem Conf.Tw_le_centralizer_u (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) :
    T ⊓ Subgroup.centralizer ({w} : Set G) ≤ Subgroup.centralizer ({t * w * t⁻¹} : Set G) := by
  intro s hs
  have hN := Conf.t_mem_normalizer_Tw c hTw h37 h38
  have hs' : t⁻¹ * s * t ∈ T ⊓ Subgroup.centralizer ({w} : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hN) s).mp hs
    simpa using this
  have hc : t⁻¹ * s * t * w = w * (t⁻¹ * s * t) :=
    Subgroup.mem_centralizer_singleton_iff.mp hs'.2
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc s * (t * w * t⁻¹) = t * (t⁻¹ * s * t * w) * t⁻¹ := by group
    _ = t * (w * (t⁻¹ * s * t)) * t⁻¹ := by rw [hc]
    _ = t * w * t⁻¹ * s := by group

theorem Conf.t_conj_u (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    t * (t * w * t⁻¹) * t⁻¹ = w := by
  have h : t * t ∈ Subgroup.centralizer ({w} : Set G) := (Conf.t_sq_mem c hTw h37 h38).2
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  calc t * (t * w * t⁻¹) * t⁻¹ = (t * t) * w * (t * t)⁻¹ := by group
    _ = w := by rw [h]; group

theorem Conf.t_inv_conj_w (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    t⁻¹ * w * t = t * w * t⁻¹ := by
  have h := Conf.t_conj_u c hTw h37 h38
  calc t⁻¹ * w * t = t⁻¹ * (t * (t * w * t⁻¹) * t⁻¹) * t := by rw [h]
    _ = t * w * t⁻¹ := by group

theorem Conf.conj_mem_CE (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {x : G} (hx : x ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G)) :
    t⁻¹ * x * t ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G) := by
  have h1 := conj_mem_centralizer (g := t⁻¹) hx.1
  have h2 := conj_mem_centralizer (g := t⁻¹) hx.2
  rw [inv_inv] at h1 h2
  rw [show t⁻¹ * (t * w * t⁻¹) * t = w by group] at h1
  rw [Conf.t_inv_conj_w c hTw h37 h38] at h2
  exact ⟨h2, h1⟩

theorem Conf.conj_mem_CE' (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {x : G} (hx : x ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.centralizer ({t * w * t⁻¹} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G) := by
  have h1 := conj_mem_centralizer (g := t) hx.1
  have h2 := conj_mem_centralizer (g := t) hx.2
  rw [Conf.t_conj_u c hTw h37 h38] at h1
  exact ⟨h2, h1⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
