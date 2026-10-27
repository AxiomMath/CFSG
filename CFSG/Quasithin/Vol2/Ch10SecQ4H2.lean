module

public import CFSG.Quasithin.Vol2.Ch10SecQ4H1
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G] {H V : Subgroup G} {t v : G}

theorem sq_mem_centralizer {U : Subgroup G} (hU2 : ∀ u ∈ U, u * u = 1) {k : G}
    (hk : ∀ x ∈ V, k * x * k⁻¹ * x⁻¹ ∈ U) (hkU : k ∈ Subgroup.centralizer (U : Set G)) :
    k ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set u := k * x * k⁻¹ * x⁻¹ with hu
  have huU : u ∈ U := hk x hx
  have hku : k * u = u * k := (Subgroup.mem_centralizer_iff.mp hkU u huU).symm
  have h1 : k * x = u * x * k := by rw [hu]; group
  rw [sq]
  symm
  calc k * k * x = k * (k * x) := by group
    _ = k * (u * x * k) := by rw [h1]
    _ = (k * u) * x * k := by group
    _ = (u * k) * x * k := by rw [hku]
    _ = u * (k * x) * k := by group
    _ = u * (u * x * k) * k := by rw [h1]
    _ = (u * u) * x * (k * k) := by group
    _ = x * (k * k) := by rw [hU2 u huU, one_mul]

theorem conjClosure_zpowers_le_self (htH : t ∈ H) : conjClosure (Subgroup.zpowers t) H ≤ H :=
  conjClosure_le fun _ hh _ hz =>
    H.mul_mem (H.mul_mem hh ((Subgroup.zpowers_le.mpr htH) hz)) (H.inv_mem hh)

theorem not_mem_centralizer_conjClosure (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    t ∉ Subgroup.centralizer (conjClosure (Subgroup.zpowers v) H : Set G) := by
  intro htU
  obtain ⟨-, hHV, hV, hred⟩ := hR
  have hUV := conjClosure_zpowers_le hHV hv
  have hU2 : ∀ u ∈ conjClosure (Subgroup.zpowers v) H, u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact hV.2 u (hUV hu)
  have hKU : conjClosure (Subgroup.zpowers t) H ≤
      Subgroup.centralizer (conjClosure (Subgroup.zpowers v) H : Set G) :=
    conjClosure_le fun h hh z hz =>
      conj_mem_centralizer_of_mem (le_normalizer_conjClosure _ H hh)
        ((Subgroup.zpowers_le.mpr htU) hz)
  have hKact := conjClosure_le_actTriv hV hHV htH hv htr
  have hKV : conjClosure (Subgroup.zpowers t) H ≤ Subgroup.centralizer (V : Set G) :=
    hred _ (conjClosure_zpowers_le_self htH) (le_normalizer_conjClosure _ H) fun d hd =>
      ⟨1, by simpa using sq_mem_centralizer hU2 (hKact hd).2 (hKU hd)⟩
  exact htC (hKV (le_conjClosure _ H (Subgroup.mem_zpowers t)))

theorem isTwoReducedIn_conjClosure (hR : IsTwoReducedIn H V) (htH : t ∈ H) (hv : v ∈ V)
    (hv1 : v ≠ 1) (htr : ∀ x ∈ V, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x * v)
    (htC : t ∉ Subgroup.centralizer (V : Set G)) :
    IsTwoReducedIn H (conjClosure (Subgroup.zpowers v) H) := by
  obtain ⟨hVH, hHV, hV, hred⟩ := hR
  have hUV := conjClosure_zpowers_le hHV hv
  have hU2 : ∀ u ∈ conjClosure (Subgroup.zpowers v) H, u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact hV.2 u (hUV hu)
  refine ⟨hUV.trans hVH, le_normalizer_conjClosure _ H, isElemAbelian_two_of_le hV hUV, ?_⟩
  intro D hDH hHD hD2
  have hKact := conjClosure_le_actTriv hV hHV htH hv htr
  have hDK : D ⊓ conjClosure (Subgroup.zpowers t) H ≤ Subgroup.centralizer (V : Set G) := by
    refine hred _ (inf_le_left.trans hDH) (fun h hh =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hHD hh, le_normalizer_conjClosure _ H hh⟩)
      fun d hd => ?_
    obtain ⟨k, hk⟩ := hD2 d hd.1
    have hsq := sq_mem_centralizer hU2 (hKact ((conjClosure _ H).pow_mem hd.2 (2 ^ k))).2 hk
    refine ⟨k + 1, ?_⟩
    rw [pow_succ, pow_mul]
    exact hsq
  obtain ⟨x₀, hx₀V, hx₀⟩ : ∃ x ∈ V, t * x * t⁻¹ = x * v := by
    rw [Subgroup.mem_centralizer_iff] at htC
    push Not at htC
    obtain ⟨x, hx, hxt⟩ := htC
    refine ⟨x, hx, (htr x hx).resolve_left fun h => hxt ?_⟩
    calc x * t = (t * x * t⁻¹) * t := by rw [h]
      _ = t * x := by group
  have hfix : ∀ d ∈ D, d * v * d⁻¹ = v := by
    intro d hd
    have hcD : d * t * d⁻¹ * t⁻¹ ∈ D := by
      have h1 : t * d⁻¹ * t⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hHD htH) d⁻¹).mp (D.inv_mem hd)
      have := D.mul_mem hd h1
      convert this using 1
      group
    have hcK : d * t * d⁻¹ * t⁻¹ ∈ conjClosure (Subgroup.zpowers t) H :=
      (conjClosure _ H).mul_mem (mem_conjClosure (hDH hd) (Subgroup.mem_zpowers t))
        ((conjClosure _ H).inv_mem (le_conjClosure _ H (Subgroup.mem_zpowers t)))
    have hc := hDK ⟨hcD, hcK⟩
    have htx₀ : t * x₀ * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hHV htH) x₀).mp hx₀V
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ htx₀
    have e1 : (d * t * d⁻¹) * x₀ * (d * t * d⁻¹)⁻¹ = x₀ * v := by
      calc (d * t * d⁻¹) * x₀ * (d * t * d⁻¹)⁻¹
          = (d * t * d⁻¹ * t⁻¹) * (t * x₀ * t⁻¹) * (d * t * d⁻¹ * t⁻¹)⁻¹ := by group
        _ = t * x₀ * t⁻¹ := by rw [← hcomm]; group
        _ = x₀ * v := hx₀
    have hy : d⁻¹ * x₀ * d⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hHV (H.inv_mem (hDH hd))) x₀).mp hx₀V
    rcases htr _ hy with h | h
    · exfalso
      apply hv1
      have e2 : (d * t * d⁻¹) * x₀ * (d * t * d⁻¹)⁻¹ = x₀ := by
        calc (d * t * d⁻¹) * x₀ * (d * t * d⁻¹)⁻¹
            = d * (t * (d⁻¹ * x₀ * d⁻¹⁻¹) * t⁻¹) * d⁻¹ := by group
          _ = d * (d⁻¹ * x₀ * d⁻¹⁻¹) * d⁻¹ := by rw [h]
          _ = x₀ := by group
      rw [e2] at e1
      calc v = x₀⁻¹ * (x₀ * v) := by group
        _ = 1 := by rw [← e1]; group
    · have e2 : (d * t * d⁻¹) * x₀ * (d * t * d⁻¹)⁻¹ = x₀ * (d * v * d⁻¹) := by
        calc (d * t * d⁻¹) * x₀ * (d * t * d⁻¹)⁻¹
            = d * (t * (d⁻¹ * x₀ * d⁻¹⁻¹) * t⁻¹) * d⁻¹ := by group
          _ = d * ((d⁻¹ * x₀ * d⁻¹⁻¹) * v) * d⁻¹ := by rw [h]
          _ = x₀ * (d * v * d⁻¹) := by group
      rw [e2] at e1
      exact mul_left_cancel e1
  intro d hd
  have hU : conjClosure (Subgroup.zpowers v) H ≤ Subgroup.centralizer ({d} : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hd' : h⁻¹ * d * h⁻¹⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hHD (H.inv_mem hh)) d).mp hd
    have hvd := hfix _ hd'
    have hcv : Commute (h⁻¹ * d * h) v := by
      simp only [inv_inv] at hvd
      calc (h⁻¹ * d * h) * v = ((h⁻¹ * d * h) * v * (h⁻¹ * d * h)⁻¹) * (h⁻¹ * d * h) := by group
        _ = v * (h⁻¹ * d * h) := by rw [hvd]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hck : Commute (h⁻¹ * d * h) (v ^ k) := hcv.zpow_right k
    symm
    calc d * (h * v ^ k * h⁻¹) = h * ((h⁻¹ * d * h) * v ^ k) * h⁻¹ := by group
      _ = h * (v ^ k * (h⁻¹ * d * h)) * h⁻¹ := by rw [hck.eq]
      _ = h * v ^ k * h⁻¹ * d := by group
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact Subgroup.mem_centralizer_singleton_iff.mp (hU hu)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
