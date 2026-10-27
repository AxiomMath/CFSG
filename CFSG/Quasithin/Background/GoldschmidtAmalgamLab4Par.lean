module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Geom
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab3Ker
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Comm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab4

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
  {c : D} {V₂ : Subgroup D}

theorem swap_conj (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) {q : D} (hqA : q ∈ pCoreOf 2 A)
    (hqB : q ∉ pCoreOf 2 B) :
    q * (x * z * x⁻¹) * q⁻¹ = x * x * z * (x * x)⁻¹ ∧
      q * (x * x * z * (x * x)⁻¹) * q⁻¹ = x * z * x⁻¹ := by
  obtain ⟨⟨hp, hp1, hpc⟩, -⟩ := V₂_elements h h2 hxB hx3 hxz hc
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hqT : q ∈ B ⊓ A := h2.gold.pCoreOf_right_le hqA
  have hqT' : q ∈ A ⊓ B := h.gold.pCoreOf_left_le hqA
  have hzz : z * z = 1 := by have := h.nat.z_sq; rwa [pow_two] at this
  have hz1sq : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hz2sq : (x * x * z * (x * x)⁻¹) * (x * x * z * (x * x)⁻¹) = 1 := by
    calc (x * x * z * (x * x)⁻¹) * (x * x * z * (x * x)⁻¹) = x * x * (z * z) * (x * x)⁻¹ := by
          group
      _ = 1 := by rw [hzz]; group
  have hcomm : ∀ u ∈ conjClosure V B, ∀ w ∈ conjClosure V B, u * w = w * u :=
    fun u hu w hw => isElemAbelian_comm h.abel hu hw
  have hz1U : x * z * x⁻¹ ∈ conjClosure V B := mem_conjClosure hxB h.nat.z_mem_V
  have hz2U : x * x * z * (x * x)⁻¹ ∈ conjClosure V B := mem_conjClosure hxxB h.nat.z_mem_V
  have h1 : q * (z * (x * z * x⁻¹)) * q⁻¹ = (z * (x * z * x⁻¹)) * c :=
    h2.nat.conj_eq_mul inf_le_left hqT hqB hp hp1 hpc
  have hqz : q * z * q⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp h.nat.z_mem.2 q hqT'
    rw [this]; group
  have hqc : q * c * q⁻¹ = c := by
    have := Subgroup.mem_centralizer_iff.mp h2.nat.z_mem.2 q hqT
    rw [this]; group
  have e : q * (z * (x * z * x⁻¹)) * q⁻¹ = (q * z * q⁻¹) * (q * (x * z * x⁻¹) * q⁻¹) := by group
  rw [e, hqz] at h1
  have h3 : q * (x * z * x⁻¹) * q⁻¹ = (x * z * x⁻¹) * c := by
    have h4 : z * (q * (x * z * x⁻¹) * q⁻¹) = z * ((x * z * x⁻¹) * c) := by
      rw [h1]; group
    exact mul_left_cancel h4
  have h5 : (x * z * x⁻¹) * c = x * x * z * (x * x)⁻¹ := by
    rw [hc]
    calc (x * z * x⁻¹) * ((x * z * x⁻¹) * (x * x * z * (x * x)⁻¹))
        = ((x * z * x⁻¹) * (x * z * x⁻¹)) * (x * x * z * (x * x)⁻¹) := by group
      _ = x * x * z * (x * x)⁻¹ := by rw [hz1sq, one_mul]
  refine ⟨h3.trans h5, ?_⟩
  have h6 : q * (x * x * z * (x * x)⁻¹) * q⁻¹ = (x * x * z * (x * x)⁻¹) * c := by
    have e2 : x * x * z * (x * x)⁻¹ = (x * z * x⁻¹) * c := h5.symm
    calc q * (x * x * z * (x * x)⁻¹) * q⁻¹
        = (q * (x * z * x⁻¹) * q⁻¹) * (q * c * q⁻¹) := by rw [e2]; group
      _ = (x * x * z * (x * x)⁻¹) * c := by rw [h3.trans h5, hqc]
  rw [h6, hc]
  have hc21 : (x * x * z * (x * x)⁻¹) * (x * z * x⁻¹) = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) :=
    hcomm _ hz2U _ hz1U
  calc (x * x * z * (x * x)⁻¹) * ((x * z * x⁻¹) * (x * x * z * (x * x)⁻¹))
      = ((x * x * z * (x * x)⁻¹) * (x * z * x⁻¹)) * (x * x * z * (x * x)⁻¹) :=
        (mul_assoc _ _ _).symm
    _ = ((x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) * (x * x * z * (x * x)⁻¹) := by rw [hc21]
    _ = (x * z * x⁻¹) * ((x * x * z * (x * x)⁻¹) * (x * x * z * (x * x)⁻¹)) := mul_assoc _ _ _
    _ = x * z * x⁻¹ := by rw [hz2sq, mul_one]

omit [Finite D] in
theorem no_conj_of_swap {a b k : D} (hab : a ≠ b) (hk : k ∈ A) (hk3 : k * k * k = 1)
    (hsw : ∀ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B → q * b * q⁻¹ = a ∧ q * a * q⁻¹ = b)
    (hfix : ∀ q ∈ pCoreOf 2 A, q ∈ pCoreOf 2 B → q * a * q⁻¹ = a ∧ q * b * q⁻¹ = b)
    (hq : ∃ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B) : k * a * k⁻¹ ≠ b := by
  intro hkab
  obtain ⟨q, hqA, hqB⟩ := hq
  have hq' : k⁻¹ * q * k ∈ pCoreOf 2 A := conj_inv_mem_pCoreOf hk hqA
  have h1 : q * b * q⁻¹ = a := (hsw q hqA hqB).1
  have key : (k⁻¹ * q * k) * a * (k⁻¹ * q * k)⁻¹ = k⁻¹ * a * k := by
    calc (k⁻¹ * q * k) * a * (k⁻¹ * q * k)⁻¹ = k⁻¹ * (q * (k * a * k⁻¹) * q⁻¹) * k := by group
      _ = k⁻¹ * a * k := by rw [hkab, h1]
  have hkk : k⁻¹ * k⁻¹ = k := by
    calc k⁻¹ * k⁻¹ = k⁻¹ * k⁻¹ * (k * k * k) := by rw [hk3, mul_one]
      _ = k := by group
  have hkk' : k * k = k⁻¹ := by
    calc k * k = k⁻¹ * (k * k * k) := by group
      _ = k⁻¹ := by rw [hk3, mul_one]
  by_cases hq'B : k⁻¹ * q * k ∈ pCoreOf 2 B
  · have h2 := (hfix _ hq' hq'B).1
    rw [key] at h2
    apply hab
    calc a = k * (k⁻¹ * a * k) * k⁻¹ := by group
      _ = k * a * k⁻¹ := by rw [h2]
      _ = b := hkab
  · have h2 := (hsw _ hq' hq'B).2
    rw [key] at h2
    have h3 : a = k⁻¹ * b * k := by
      calc a = k⁻¹ * (k * a * k⁻¹) * k := by group
        _ = k⁻¹ * b * k := by rw [hkab]
    have h4 : k * b * k⁻¹ = b := by
      calc k * b * k⁻¹ = (k⁻¹ * k⁻¹) * b * (k * k) := by rw [hkk, hkk']
        _ = k⁻¹ * (k⁻¹ * b * k) * k := by group
        _ = k⁻¹ * a * k := by rw [← h3]
        _ = b := h2
    apply hab
    calc a = k⁻¹ * b * k := h3
      _ = k⁻¹ * (k * b * k⁻¹) * k := by rw [h4]
      _ = b := by group

omit [Finite D] in
theorem fix_other {a b k : D} (hab : a ≠ b) (hk : k ∈ A)
    (hsw : ∀ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B → q * a * q⁻¹ = b)
    (hfix : ∀ q ∈ pCoreOf 2 A, q ∈ pCoreOf 2 B → q * a * q⁻¹ = a)
    (hq : ∃ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B) (hka : k * a * k⁻¹ = a) : k * b * k⁻¹ = b := by
  obtain ⟨q, hqA, hqB⟩ := hq
  have hq' : k⁻¹ * q * k ∈ pCoreOf 2 A := conj_inv_mem_pCoreOf hk hqA
  have key : b = k * ((k⁻¹ * q * k) * a * (k⁻¹ * q * k)⁻¹) * k⁻¹ := by
    calc b = q * a * q⁻¹ := (hsw q hqA hqB).symm
      _ = q * (k * a * k⁻¹) * q⁻¹ := by rw [hka]
      _ = k * ((k⁻¹ * q * k) * a * (k⁻¹ * q * k)⁻¹) * k⁻¹ := by group
  by_cases hq'B : k⁻¹ * q * k ∈ pCoreOf 2 B
  · rw [hfix _ hq' hq'B, hka] at key
    exact absurd key.symm hab
  · rw [hsw _ hq' hq'B] at key
    exact key.symm

theorem centralizes_c_of_fix (h : OneSide A B z V) (h2 : OneSide B A c V₂) {k : D} (hk : k ∈ A)
    (hkT : k ∉ A ⊓ B) (hkc : k * c * k⁻¹ = c) : ∀ g ∈ A, g * c * g⁻¹ = c := by
  let C : Subgroup D := A ⊓ Subgroup.centralizer ({c} : Set D)
  have hTC : A ⊓ B ≤ C := fun t ht => ⟨ht.1, Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have ht' : t ∈ B ⊓ A := by rw [inf_comm]; exact ht
    exact (Subgroup.mem_centralizer_iff.mp h2.nat.z_mem.2 t ht').symm⟩
  have hkC : k ∈ C := ⟨hk, Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mul_eq_of_conj_eq hkc).symm⟩
  have hAC : A ≤ C := h.gold.vertex_left.le_of_not_mem hTC inf_le_left hkC hkT
  intro g hg
  have h3 : c * g = g * c := Subgroup.mem_centralizer_iff.mp (hAC hg).2 c rfl
  calc g * c * g⁻¹ = (c * g) * g⁻¹ := by rw [h3]
    _ = c := by group

theorem swap_data (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) :
    (∃ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B) ∧
      (∀ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B →
        q * (x * z * x⁻¹) * q⁻¹ = x * x * z * (x * x)⁻¹ ∧
          q * (x * x * z * (x * x)⁻¹) * q⁻¹ = x * z * x⁻¹) ∧
      (∀ q ∈ pCoreOf 2 A, q ∈ pCoreOf 2 B →
        q * (x * z * x⁻¹) * q⁻¹ = x * z * x⁻¹ ∧
          q * (x * x * z * (x * x)⁻¹) * q⁻¹ = x * x * z * (x * x)⁻¹) := by
  refine ⟨?_, fun q hqA hqB => swap_conj h h2 hxB hx3 hxz hc hqA hqB, ?_⟩
  · have hne : pCoreOf 2 B ≠ pCoreOf 2 A := h2.nat.pCoreOf_ne h2.gold
    have hnot : ¬ pCoreOf 2 A ≤ pCoreOf 2 B := h2.gold.not_pCoreOf_right_le_left hne
    by_contra hcon
    push Not at hcon
    exact hnot fun q hq => hcon q hq
  · have hzQB : z ∈ Subgroup.centralizer (pCoreOf 2 B : Set D) :=
      Subgroup.centralizer_le h.gold.pCoreOf_right_le h.nat.z_mem.2
    have hz1 := conj_mem_centralizer' (le_normalizer_pCoreOf 2 B hxB) hzQB
    have hz2 := conj_mem_centralizer' (le_normalizer_pCoreOf 2 B (B.mul_mem hxB hxB)) hzQB
    intro q _ hqB
    have e1 : q * (x * z * x⁻¹) = (x * z * x⁻¹) * q := Subgroup.mem_centralizer_iff.mp hz1 q hqB
    have e2 : q * (x * x * z * (x * x)⁻¹) = (x * x * z * (x * x)⁻¹) * q :=
      Subgroup.mem_centralizer_iff.mp hz2 q hqB
    constructor
    · rw [e1]; group
    · rw [e2]; group

theorem zeta_false (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) (hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c)
    {k : D} (hk : k ∈ A) (hk3 : k * k * k = 1) (hkT : k ∉ A ⊓ B) {ζ₂ ζ : D}
    (hζ₂ : ζ₂ = x * z * x⁻¹ ∨ ζ₂ = x * x * z * (x * x)⁻¹)
    (hζ : ζ = x * z * x⁻¹ ∨ ζ = x * x * z * (x * x)⁻¹) (heq : ζ₂ = k * ζ * k⁻¹) : False := by
  obtain ⟨hq, hsw, hfix⟩ := swap_data h h2 hxB hx3 hxz hc
  obtain ⟨-, -, -, -, h12⟩ := c_facts hx3 hxz h.nat.z_ne
  obtain ⟨g, hgA, hg⟩ := hAc
  have hcfix : ∀ {a b : D}, a ≠ b → (∀ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B → q * a * q⁻¹ = b) →
      (∀ q ∈ pCoreOf 2 A, q ∈ pCoreOf 2 B → q * a * q⁻¹ = a) → c = a * b ∨ c = b * a →
      k * a * k⁻¹ = a → a * b = b * a → False := by
    intro a b hab hs hf hcab hka hcom
    have hkb := fix_other hab hk hs hf hq hka
    have hkc : k * c * k⁻¹ = c := by
      rcases hcab with e | e
      · rw [e]
        calc k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
          _ = a * b := by rw [hka, hkb]
      · rw [e]
        calc k * (b * a) * k⁻¹ = (k * b * k⁻¹) * (k * a * k⁻¹) := by group
          _ = b * a := by rw [hka, hkb]
    exact hg (centralizes_c_of_fix h h2 hk hkT hkc g hgA)
  have hcomm : ∀ u ∈ conjClosure V B, ∀ w ∈ conjClosure V B, u * w = w * u :=
    fun u hu w hw => isElemAbelian_comm h.abel hu hw
  have hz1U : x * z * x⁻¹ ∈ conjClosure V B := mem_conjClosure hxB h.nat.z_mem_V
  have hz2U : x * x * z * (x * x)⁻¹ ∈ conjClosure V B :=
    mem_conjClosure (B.mul_mem hxB hxB) h.nat.z_mem_V
  have hc21 : (x * x * z * (x * x)⁻¹) * (x * z * x⁻¹) = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) :=
    hcomm _ hz2U _ hz1U
  rcases hζ₂ with rfl | rfl <;> rcases hζ with rfl | rfl
  · exact hcfix h12 (fun q hqA hqB => (hsw q hqA hqB).1) (fun q hqA hqB => (hfix q hqA hqB).1)
      (Or.inl hc) heq.symm hc21.symm
  · exact no_conj_of_swap (A := A) (B := B) (a := x * x * z * (x * x)⁻¹) (b := x * z * x⁻¹)
      (Ne.symm h12) hk hk3 (fun q hqA hqB => ⟨(hsw q hqA hqB).1, (hsw q hqA hqB).2⟩)
      (fun q hqA hqB => ⟨(hfix q hqA hqB).2, (hfix q hqA hqB).1⟩) hq heq.symm
  · exact no_conj_of_swap (A := A) (B := B) (a := x * z * x⁻¹) (b := x * x * z * (x * x)⁻¹) h12
      hk hk3 (fun q hqA hqB => ⟨(hsw q hqA hqB).2, (hsw q hqA hqB).1⟩)
      (fun q hqA hqB => ⟨(hfix q hqA hqB).1, (hfix q hqA hqB).2⟩) hq heq.symm
  · exact hcfix (Ne.symm h12) (fun q hqA hqB => (hsw q hqA hqB).2)
      (fun q hqA hqB => (hfix q hqA hqB).2) (Or.inr hc) heq.symm hc21

omit [Finite D] in
theorem mul_comm_of_comm_eq_one {a b : D} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

theorem pair_core (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹))
    (hU4 : conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A)
    (hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c) {e₂ e v₂ v k : D} (he₂ : e₂ = x ∨ e₂ = x * x)
    (he : e = x ∨ e = x * x) (hv₂ : v₂ ∈ V) (hv : v ∈ V) (hk : k ∈ A) (hk3 : k * k * k = 1)
    (hkT : k ∉ A ⊓ B) :
    (e₂ * v₂ * e₂⁻¹) * (k * (e * v * e⁻¹) * k⁻¹) =
      (k * (e * v * e⁻¹) * k⁻¹) * (e₂ * v₂ * e₂⁻¹) := by
  have he₂B : e₂ ∈ B := by rcases he₂ with rfl | rfl; exacts [hxB, B.mul_mem hxB hxB]
  have heB : e ∈ B := by rcases he with rfl | rfl; exacts [hxB, B.mul_mem hxB hxB]
  have hzz : z * z = 1 := by have := h.nat.z_sq; rwa [pow_two] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hu : e * v * e⁻¹ ∈ conjClosure V B := mem_conjClosure heB hv
  have hu₂ : e₂ * v₂ * e₂⁻¹ ∈ conjClosure V B := mem_conjClosure he₂B hv₂
  have hKA : ∀ g ∈ A, ∀ u ∈ conjClosure V B, g * u * g⁻¹ ∈ pCoreOf 2 B := fun g hg u hu' =>
    (coreIn_le_right _ _ ((Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ hg) u).mp
      (hU4 hu'))).2
  have hw : k * (e * v * e⁻¹) * k⁻¹ ∈ pCoreOf 2 B := hKA k hk _ hu
  have hw' : k⁻¹ * (e₂ * v₂ * e₂⁻¹) * k ∈ pCoreOf 2 B := by
    have := hKA k⁻¹ (A.inv_mem hk) _ hu₂
    rwa [inv_inv] at this
  have iden : ∀ (u₂ u k : D), u₂ * (k * u * k⁻¹) * u₂⁻¹ * (k * u * k⁻¹)⁻¹ =
      k * (u * (k⁻¹ * u₂ * k) * u⁻¹ * (k⁻¹ * u₂ * k)⁻¹)⁻¹ * k⁻¹ := fun u₂ u k => by group
  rcases comm_B_side h he₂B hv₂ hw with hB1 | hB1
  · exact mul_comm_of_comm_eq_one hB1
  · rcases comm_B_side h heB hv hw' with hB2 | hB2
    · apply mul_comm_of_comm_eq_one
      rw [iden, hB2]
      group
    · exfalso
      have hζ : e₂ * z * e₂⁻¹ = k * (e * z * e⁻¹) * k⁻¹ := by
        rw [← hB1, iden, hB2]
        calc k * (e * z * e⁻¹)⁻¹ * k⁻¹ = k * (e * z⁻¹ * e⁻¹) * k⁻¹ := by group
          _ = k * (e * z * e⁻¹) * k⁻¹ := by rw [hzinv]
      exact zeta_false h h2 hxB hx3 hxz hc hAc hk hk3 hkT
        (by rcases he₂ with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl])
        (by rcases he with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]) hζ

theorem gen_form (h : OneSide A B z V) {x : D} (hxB : x ∈ B) (hxT : x ∉ A ⊓ B)
    (hx2T : x * x ∉ A ⊓ B) {g v : D} (hg : g ∈ B) (hgT : g ∉ A ⊓ B) (hv : v ∈ V) :
    ∃ e v' : D, (e = x ∨ e = x * x) ∧ v' ∈ V ∧ g * v * g⁻¹ = e * v' * e⁻¹ := by
  have hvT : ∀ t ∈ A ⊓ B, t * v * t⁻¹ ∈ V := fun t ht =>
    (Subgroup.mem_normalizer_iff.mp (h.nat.reduced.2.1 ht.1) v).mp hv
  rcases coset_decomp h.gold.relIndex_right hxB hxT hx2T hg with hgT' | ⟨t, htT, rfl⟩ |
      ⟨t, htT, rfl⟩
  · exact absurd hgT' hgT
  · exact ⟨x, t * v * t⁻¹, Or.inl rfl, hvT t htT, by group⟩
  · exact ⟨x * x, t * v * t⁻¹, Or.inr rfl, hvT t htT, by group⟩

theorem k_form (h : OneSide A B z V) :
    ∃ y ∈ A, y * y * y = 1 ∧ y ∉ A ⊓ B ∧ y * y ∉ A ⊓ B ∧
      ∀ k ∈ A, k ∉ A ⊓ B → ∃ k₀ t : D, (k₀ = y ∨ k₀ = y * y) ∧ t ∈ A ⊓ B ∧ k = k₀ * t := by
  obtain ⟨y, hyA, hy3⟩ := h.gold.vertex_left.exists_order_three
  have hyT := h.gold.vertex_left.not_mem_of_orderOf hy3
  have hy2T := h.gold.vertex_left.sq_not_mem_of_orderOf hy3
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  refine ⟨y, hyA, hy3', hyT, hy2T, fun k hk hkT => ?_⟩
  rcases coset_decomp h.gold.relIndex_left hyA hyT hy2T hk with hT | ⟨t, htT, rfl⟩ |
      ⟨t, htT, rfl⟩
  · exact absurd hT hkT
  · exact ⟨y, t, Or.inl rfl, htT, rfl⟩
  · exact ⟨y * y, t, Or.inr rfl, htT, rfl⟩

theorem pair_N (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹))
    (hU4 : conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A)
    (hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c) {g₂ g v₂ v k : D} (hg₂ : g₂ ∈ B) (hg : g ∈ B)
    (hv₂ : v₂ ∈ V) (hv : v ∈ V) (hk : k ∈ A) :
    (g₂ * v₂ * g₂⁻¹) * (k * (g * v * g⁻¹) * k⁻¹) =
      (k * (g * v * g⁻¹) * k⁻¹) * (g₂ * v₂ * g₂⁻¹) := by
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
  have hvT : ∀ t ∈ A ⊓ B, ∀ w ∈ V, t * w * t⁻¹ ∈ V := fun t ht w hw =>
    (Subgroup.mem_normalizer_iff.mp (h.nat.reduced.2.1 ht.1) w).mp hw
  have hu₂ : g₂ * v₂ * g₂⁻¹ ∈ conjClosure V B := mem_conjClosure hg₂ hv₂
  have hu : g * v * g⁻¹ ∈ conjClosure V B := mem_conjClosure hg hv
  have hu₂QA : g₂ * v₂ * g₂⁻¹ ∈ pCoreOf 2 A := h.U_le_Q_A hu₂
  have hwQA : k * (g * v * g⁻¹) * k⁻¹ ∈ pCoreOf 2 A :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hk) _).mp (h.U_le_Q_A hu)
  by_cases hg₂T : g₂ ∈ A ⊓ B
  · have hu₂V : g₂ * v₂ * g₂⁻¹ ∈ V := hvT g₂ hg₂T v₂ hv₂
    exact (Subgroup.mem_centralizer_iff.mp (h.nat.le_center hu₂V).2 _ hwQA).symm
  by_cases hgT : g ∈ A ⊓ B
  · have huV : g * v * g⁻¹ ∈ V := hvT g hgT v hv
    have hwV : k * (g * v * g⁻¹) * k⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.nat.reduced.2.1 hk) _).mp huV
    exact Subgroup.mem_centralizer_iff.mp (h.nat.le_center hwV).2 _ hu₂QA
  by_cases hkT : k ∈ A ⊓ B
  · have hwU : k * (g * v * g⁻¹) * k⁻¹ ∈ conjClosure V B := conj_mem_conjClosure_self hkT.2 hu
    exact isElemAbelian_comm h.abel hu₂ hwU
  obtain ⟨y, hyA, hy3, hyT, hy2T, hkf⟩ := k_form h
  obtain ⟨k₀, t, hk₀, htT, rfl⟩ := hkf k hk hkT
  obtain ⟨e₂, v₂', he₂, hv₂', h₂eq⟩ := gen_form h hxB hxT hx2T hg₂ hg₂T hv₂
  have hg'B : t * g ∈ B := B.mul_mem htT.2 hg
  have hg'T : t * g ∉ A ⊓ B := fun hmem => hgT (by
    have := (A ⊓ B).mul_mem ((A ⊓ B).inv_mem htT) hmem
    simpa using this)
  obtain ⟨e, v', he, hv', heq⟩ := gen_form h hxB hxT hx2T hg'B hg'T hv
  have hk₀A : k₀ ∈ A := by rcases hk₀ with rfl | rfl; exacts [hyA, A.mul_mem hyA hyA]
  have hk₀3 : k₀ * k₀ * k₀ = 1 := by
    rcases hk₀ with rfl | rfl
    · exact hy3
    · calc y * y * (y * y) * (y * y) = (y * y * y) * (y * y * y) := by group
        _ = 1 := by rw [hy3, one_mul]
  have hk₀T : k₀ ∉ A ⊓ B := by rcases hk₀ with rfl | rfl; exacts [hyT, hy2T]
  rw [h₂eq]
  have e1 : k₀ * t * (g * v * g⁻¹) * (k₀ * t)⁻¹ = k₀ * ((t * g) * v * (t * g)⁻¹) * k₀⁻¹ := by
    group
  rw [e1, heq]
  exact pair_core h h2 hxB hx3 hxz hc hU4 hAc he₂ he hv₂' hv' hk₀A hk₀3 hk₀T

theorem N_le_centralizer (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D} (hxB : x ∈ B)
    (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹))
    (hU4 : conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A)
    (hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c) :
    conjClosure (conjClosure V B) A ≤ Subgroup.centralizer (conjClosure V B : Set D) := by
  have hA : ∀ k ∈ A, ∀ g ∈ B, ∀ v ∈ V,
      conjClosure V B ≤ Subgroup.centralizer ({k * (g * v * g⁻¹) * k⁻¹} : Set D) := by
    intro k hk g hg v hv
    refine conjClosure_le fun g₂ hg₂ v₂ hv₂ => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (pair_N h h2 hxB hx3 hxz hc hU4 hAc hg₂ hg hv₂ hv hk).symm
  refine conjClosure_le fun k hk u hu => ?_
  have hS : conjClosure V B ≤
      (Subgroup.centralizer (conjClosure V B : Set D)).comap (MulAut.conj k).toMonoidHom := by
    refine conjClosure_le fun g hg v hv => ?_
    show k * (g * v * g⁻¹) * k⁻¹ ∈ Subgroup.centralizer (conjClosure V B : Set D)
    exact Subgroup.mem_centralizer_iff.mpr fun u' hu' =>
      (Subgroup.mem_centralizer_iff.mp (hA k hk g hg v hv hu') _ (Set.mem_singleton _)).symm
  exact hS hu

theorem five_le_critDist_of_moves_moves (h : OneSide A B z V) (h2 : OneSide B A c V₂) {x : D}
    (hxB : x ∈ B) (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹))
    (hU4 : conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A)
    (hAc : ∃ g ∈ A, g * c * g⁻¹ ≠ c) : 5 ≤ critDist (A ⊔ B) A B V := by
  have hN := N_le_centralizer h h2 hxB hx3 hxz hc hU4 hAc
  have hNK : conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A :=
    conjClosure_le fun k hk u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ hk) u).mp (hU4 hu)
  have hNQB : conjClosure (conjClosure V B) A ≤ pCoreOf 2 B :=
    hNK.trans ((coreIn_le_right _ _).trans inf_le_right)
  have hNKB : conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
    rw [← GoldAmLab3.pCoreOf_inf_centralizer_eq_coreIn h]
    exact le_inf hNQB hN
  rw [le_critDist_iff (h.gold.amalgamHypV h.nat) h.nat.natural.ne_bot (by norm_num),
    le_ballStab_five_iff rfl h.nat.reduced.2.1]
  have hVA : V ≤ A := h.nat.le_pCoreOf.trans (pCoreOf_le 2 A)
  have hVB : V ≤ B := h.hVQ.trans (pCoreOf_le 2 B)
  have hUA : conjClosure V B ≤ A := h.U_le_Q_A.trans (pCoreOf_le 2 A)
  have hNB : conjClosure (conjClosure V B) A ≤ B := hNQB.trans (pCoreOf_le 2 B)
  have hN₂ : conjClosure (conjClosure (conjClosure V B) A) B ≤
      coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B :=
    conjClosure_le fun g hg w hw =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ hg) w).mp (hNKB hw)
  have hN₂QA : conjClosure (conjClosure (conjClosure V B) A) B ≤ pCoreOf 2 A :=
    hN₂.trans ((coreIn_le_right _ _).trans inf_le_left)
  have hN₂A : conjClosure (conjClosure (conjClosure V B) A) B ≤ A :=
    hN₂QA.trans (pCoreOf_le 2 A)
  have hN₃ : conjClosure (conjClosure (conjClosure (conjClosure V B) A) B) A ≤ pCoreOf 2 A :=
    conjClosure_le fun k hk w hw =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hk) w).mp (hN₂QA hw)
  have hN₃B : conjClosure (conjClosure (conjClosure (conjClosure V B) A) B) A ≤ B :=
    hN₃.trans (h.gold.pCoreOf_left_le.trans inf_le_right)
  exact ⟨hVA, hVB, hUA, hNB, hN₂A, hN₃B⟩

end GoldAmLab4

end F6

end CFSG.Quasithin
