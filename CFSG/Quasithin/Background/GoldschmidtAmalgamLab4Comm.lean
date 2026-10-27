module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Swap

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab4

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
  {c : D} {V₂ : Subgroup D}

theorem comm_B_side (h : OneSide A B z V) {e v w : D} (he : e ∈ B) (hv : v ∈ V)
    (hw : w ∈ pCoreOf 2 B) :
    (e * v * e⁻¹) * w * (e * v * e⁻¹)⁻¹ * w⁻¹ = 1 ∨
      (e * v * e⁻¹) * w * (e * v * e⁻¹)⁻¹ * w⁻¹ = e * z * e⁻¹ := by
  have hw'Q : e⁻¹ * w * e ∈ pCoreOf 2 B := conj_inv_mem_pCoreOf he hw
  have hw'T : e⁻¹ * w * e ∈ A ⊓ B := h.gold.pCoreOf_right_le hw'Q
  have hk := h.nat.conj_cases inf_le_left hw'T (V.inv_mem hv)
  have e1 : (e * v * e⁻¹) * w * (e * v * e⁻¹)⁻¹ * w⁻¹ =
      e * (v * ((e⁻¹ * w * e) * v⁻¹ * (e⁻¹ * w * e)⁻¹)) * e⁻¹ := by group
  rcases hk with hk | hk
  · left
    rw [e1, hk]
    group
  · right
    rw [e1, hk]
    group

theorem comm_A_side (h2 : OneSide B A c V₂) {u k y : D} (hu : u ∈ pCoreOf 2 A) (hk : k ∈ A)
    (hy : y ∈ V₂) :
    u * (k * y * k⁻¹) * u⁻¹ * (k * y * k⁻¹)⁻¹ = 1 ∨
      u * (k * y * k⁻¹) * u⁻¹ * (k * y * k⁻¹)⁻¹ = k * c * k⁻¹ := by
  have hu'' : k⁻¹ * u * k ∈ pCoreOf 2 A := conj_inv_mem_pCoreOf hk hu
  have hu''T : k⁻¹ * u * k ∈ B ⊓ A := h2.gold.pCoreOf_right_le hu''
  have hcy : y * c = c * y := h2.nat.comm_of_mem hy h2.nat.z_mem_V
  have e1 : u * (k * y * k⁻¹) * u⁻¹ * (k * y * k⁻¹)⁻¹ =
      k * (((k⁻¹ * u * k) * y * (k⁻¹ * u * k)⁻¹) * y⁻¹) * k⁻¹ := by group
  rcases h2.nat.conj_cases inf_le_left hu''T hy with hk' | hk'
  · left
    rw [e1, hk']
    group
  · right
    rw [e1, hk']
    have : y * c * y⁻¹ = c := by rw [hcy]; group
    rw [this]

theorem conj_c_mem_centralizer (h2 : OneSide B A c V₂) {k : D} (hk : k ∈ A) :
    k * c * k⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 A : Set D) := by
  have hc : c ∈ Subgroup.centralizer (pCoreOf 2 A : Set D) :=
    Subgroup.centralizer_le (h2.gold.pCoreOf_right_le) h2.nat.z_mem.2
  exact conj_mem_centralizer' (le_normalizer_pCoreOf 2 A hk) hc

omit [Finite D] in
theorem V₂_elements (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) :
    (z * (x * z * x⁻¹) ∈ V₂ ∧ z * (x * z * x⁻¹) ≠ 1 ∧ z * (x * z * x⁻¹) ≠ c) ∧
      ((x * x * z * (x * x)⁻¹) * z ∈ V₂ ∧ (x * x * z * (x * x)⁻¹) * z ≠ 1 ∧
        (x * x * z * (x * x)⁻¹) * z ≠ c) := by
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hzV : z ∈ V := h.nat.z_mem_V
  have hzz : z * z = 1 := by have := h.nat.z_sq; rwa [pow_two] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hcomm : ∀ u ∈ conjClosure V B, ∀ w ∈ conjClosure V B, u * w = w * u :=
    fun u hu w hw => isElemAbelian_comm h.abel hu hw
  have hz1U : x * z * x⁻¹ ∈ conjClosure V B := mem_conjClosure hxB hzV
  have hz2U : x * x * z * (x * x)⁻¹ ∈ conjClosure V B := mem_conjClosure hxxB hzV
  have hzU : z ∈ conjClosure V B := le_conjClosure V B hzV
  obtain ⟨-, -, hz1, hz2, -⟩ := c_facts hx3 hxz h.nat.z_ne
  have hVmem : ∀ g ∈ B, g * c * g⁻¹ ∈ V₂ := fun g hg => by
    rw [h2.nat.V_eq]
    exact mem_conjClosure hg (Subgroup.mem_zpowers c)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · have hv : x * x * c * (x * x)⁻¹ = z * (x * z * x⁻¹) := by
      rw [hc]
      calc x * x * ((x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) * (x * x)⁻¹
          = (x * x * x) * z * (x * x * x)⁻¹ * ((x * x * x * x) * z * (x * x * x * x)⁻¹) := by
            group
        _ = z * (x * z * x⁻¹) := by rw [hx3]; group
    rw [← hv]
    exact hVmem (x * x) hxxB
  · intro h1
    exact hz1 (hzinv.symm.trans (inv_eq_of_mul_eq_one_right h1))
  · rw [hc]
    intro h1
    have h2' : (x * z * x⁻¹) * z = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) := by
      rw [hcomm _ hz1U z hzU, h1]
    exact hz2 (mul_left_cancel h2')
  · have hv : x * c * x⁻¹ = (x * x * z * (x * x)⁻¹) * z := by
      rw [hc]
      calc x * ((x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) * x⁻¹
          = (x * x * z * (x * x)⁻¹) * ((x * x * x) * z * (x * x * x)⁻¹) := by group
        _ = (x * x * z * (x * x)⁻¹) * z := by rw [hx3]; group
    rw [← hv]
    exact hVmem x hxB
  · intro h1
    exact hz2 (hzinv.symm.trans (inv_eq_of_mul_eq_one_left h1))
  · rw [hc]
    intro h1
    have h2' : (x * x * z * (x * x)⁻¹) * z = (x * x * z * (x * x)⁻¹) * (x * z * x⁻¹) := by
      rw [hcomm _ hz2U _ hz1U, h1]
    exact hz1 (mul_left_cancel h2')

theorem conj_z_not_mem_centralizer (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D}
    (hxB : x ∈ B) (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) :
    x * z * x⁻¹ ∉ Subgroup.centralizer (pCoreOf 2 A : Set D) ∧
      x * x * z * (x * x)⁻¹ ∉ Subgroup.centralizer (pCoreOf 2 A : Set D) := by
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 A : Set D) :=
    (h.nat.le_center h.nat.z_mem_V).2
  obtain ⟨⟨hp, hp1, hpc⟩, ⟨hp', hp1', hpc'⟩⟩ := V₂_elements h h2 hxB hx3 hxz hc
  exact ⟨fun hz1C => not_mem_centralizer_of_mem h2 hp hp1 hpc (Subgroup.mul_mem _ hzC hz1C),
    fun hz2C => not_mem_centralizer_of_mem h2 hp' hp1' hpc' (Subgroup.mul_mem _ hz2C hzC)⟩

theorem pair_comm (h : OneSide A B z V) (h2 : OneSide B A c V₂) {e v k y : D} (he : e ∈ B)
    (hez : e * z * e⁻¹ ∉ Subgroup.centralizer (pCoreOf 2 A : Set D)) (hv : v ∈ V) (hk : k ∈ A)
    (hy : y ∈ V₂) : (e * v * e⁻¹) * (k * y * k⁻¹) = (k * y * k⁻¹) * (e * v * e⁻¹) := by
  have hw : k * y * k⁻¹ ∈ conjClosure V₂ A := mem_conjClosure hk hy
  have hwQB : k * y * k⁻¹ ∈ pCoreOf 2 B := h2.U_le_Q_A hw
  have hu : e * v * e⁻¹ ∈ conjClosure V B := mem_conjClosure he hv
  have huQA : e * v * e⁻¹ ∈ pCoreOf 2 A := h.U_le_Q_A hu
  have key : (e * v * e⁻¹) * (k * y * k⁻¹) * (e * v * e⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹ = 1 →
      (e * v * e⁻¹) * (k * y * k⁻¹) = (k * y * k⁻¹) * (e * v * e⁻¹) := fun h1 => by
    calc (e * v * e⁻¹) * (k * y * k⁻¹)
        = ((e * v * e⁻¹) * (k * y * k⁻¹) * (e * v * e⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹) *
          ((k * y * k⁻¹) * (e * v * e⁻¹)) := by group
      _ = (k * y * k⁻¹) * (e * v * e⁻¹) := by rw [h1, one_mul]
  rcases comm_A_side h2 huQA hk hy with hA | hA
  · exact key hA
  · rcases comm_B_side h he hv hwQB with hB | hB
    · exact key hB
    · exact absurd (hB.symm.trans hA ▸ conj_c_mem_centralizer h2 hk) hez

theorem gen_comm (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) {g v k y : D} (hg : g ∈ B) (hv : v ∈ V)
    (hk : k ∈ A) (hy : y ∈ V₂) : (g * v * g⁻¹) * (k * y * k⁻¹) = (k * y * k⁻¹) * (g * v * g⁻¹) := by
  have hxT : x ∉ A ⊓ B := fun hxT => hxz (by
    have := Subgroup.mem_centralizer_iff.mp h.nat.z_mem.2 x hxT
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [this]
      _ = z := by group)
  have hx2T : x * x ∉ A ⊓ B := fun hxx => hxT (by
    have e : x = (x * x) * (x * x) := by
      calc x = (x * x * x) * x := by rw [hx3, one_mul]
        _ = (x * x) * (x * x) := by group
    rw [e]
    exact (A ⊓ B).mul_mem hxx hxx)
  obtain ⟨hz1, hz2⟩ := conj_z_not_mem_centralizer h h2 hxB hx3 hxz hc
  have hvT : ∀ t ∈ A ⊓ B, t * v * t⁻¹ ∈ V := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp (h.nat.reduced.2.1 ht.1) v).mp hv
  rcases coset_decomp h.gold.relIndex_right hxB hxT hx2T hg with hgT | ⟨t, htT, rfl⟩ |
      ⟨t, htT, rfl⟩
  · have hu : g * v * g⁻¹ ∈ V := hvT g hgT
    have hw : k * y * k⁻¹ ∈ conjClosure V₂ A := mem_conjClosure hk hy
    have hwQA : k * y * k⁻¹ ∈ pCoreOf 2 A := h2.U_le_Q_B hw
    exact (Subgroup.mem_centralizer_iff.mp (h.nat.le_center hu).2 _ hwQA).symm
  · have e1 : x * t * v * (x * t)⁻¹ = x * (t * v * t⁻¹) * x⁻¹ := by group
    rw [e1]
    exact pair_comm h h2 hxB hz1 (hvT t htT) hk hy
  · have e1 : x * x * t * v * (x * x * t)⁻¹ = x * x * (t * v * t⁻¹) * (x * x)⁻¹ := by group
    rw [e1]
    exact pair_comm h h2 (B.mul_mem hxB hxB) hz2 (hvT t htT) hk hy

theorem U_comm_U₂ (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) :
    ∀ u ∈ conjClosure V B, ∀ w ∈ conjClosure V₂ A, u * w = w * u := by
  have hgen : ∀ k ∈ A, ∀ y ∈ V₂,
      conjClosure V B ≤ Subgroup.centralizer ({k * y * k⁻¹} : Set D) := by
    intro k hk y hy
    refine conjClosure_le fun g hg v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (gen_comm h h2 hxB hx3 hxz hc hg hv hk hy).symm
  have hU₂ : conjClosure V₂ A ≤ Subgroup.centralizer (conjClosure V B : Set D) := by
    refine conjClosure_le fun k hk y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hgen k hk y hy hu) _ (Set.mem_singleton _)).symm
  intro u hu w hw
  exact Subgroup.mem_centralizer_iff.mp (hU₂ hw) u hu

end GoldAmLab4

end F6

end CFSG.Quasithin
