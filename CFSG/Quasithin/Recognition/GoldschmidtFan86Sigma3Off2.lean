module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Gen

public section

namespace CFSG.Quasithin.Fan86.Sigma3

variable {H : Type*} [Group H] {S : Subgroup H}

def nSub (x : H) (E : Subgroup H) (hE : E.Normal) (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Subgroup H where
  carrier := {n | ∃ e ∈ E, n = e * (x * e * x⁻¹)}
  one_mem' := ⟨1, E.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩
    refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, ?_⟩
    have h1 : x * e₁ * x⁻¹ ∈ E := hE.conj_mem e₁ he₁ x
    have h2 := hc _ h1 e₂ he₂
    calc e₁ * (x * e₁ * x⁻¹) * (e₂ * (x * e₂ * x⁻¹))
        = e₁ * ((x * e₁ * x⁻¹) * e₂) * (x * e₂ * x⁻¹) := by group
      _ = e₁ * (e₂ * (x * e₁ * x⁻¹)) * (x * e₂ * x⁻¹) := by rw [h2]
      _ = e₁ * e₂ * (x * (e₁ * e₂) * x⁻¹) := by
        have h3 := hc _ h1 _ (hE.conj_mem e₂ he₂ x)
        calc e₁ * (e₂ * (x * e₁ * x⁻¹)) * (x * e₂ * x⁻¹)
            = e₁ * e₂ * ((x * e₁ * x⁻¹) * (x * e₂ * x⁻¹)) := by group
          _ = e₁ * e₂ * (x * (e₁ * e₂) * x⁻¹) := by group
  inv_mem' := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e⁻¹, E.inv_mem he, ?_⟩
    have h1 : x * e * x⁻¹ ∈ E := hE.conj_mem e he x
    have h2 := hc e he _ h1
    calc (e * (x * e * x⁻¹))⁻¹ = (x * e * x⁻¹)⁻¹ * e⁻¹ := by group
      _ = e⁻¹ * (x * e * x⁻¹)⁻¹ := by
        have := hc _ (E.inv_mem h1) e⁻¹ (E.inv_mem he)
        exact this
      _ = e⁻¹ * (x * e⁻¹ * x⁻¹) := by group

theorem nSub_le {x : H} {E : Subgroup H} {hE : E.Normal} {hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a} :
    nSub x E hE hc ≤ E := by
  rintro _ ⟨e, he, rfl⟩
  exact E.mul_mem he (hE.conj_mem e he x)

theorem nSub_fix {x : H} (hx3 : x * x * x = 1) {E : Subgroup H} {hE : E.Normal}
    {hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a} (hsq : ∀ e ∈ E, e * e = 1) {n : H}
    (hn : n ∈ nSub x E hE hc) (hfix : x * n * x⁻¹ = n) : n = 1 := by
  obtain ⟨e, he, rfl⟩ := hn
  have h1 : x * e * x⁻¹ ∈ E := hE.conj_mem e he x
  have h2 : x * (x * e * x⁻¹) * x⁻¹ ∈ E := hE.conj_mem _ h1 x
  have h3 : x * (x * e * x⁻¹) * x⁻¹ = e := by
    have h4 : (x * e * x⁻¹) * (x * (x * e * x⁻¹) * x⁻¹) = e * (x * e * x⁻¹) := by
      rw [← hfix]; group
    have h5 := hc _ h1 e he
    have h6 : (x * e * x⁻¹) * (x * (x * e * x⁻¹) * x⁻¹) = (x * e * x⁻¹) * e := by
      rw [h4, h5]
    exact mul_left_cancel h6
  have h7 : x * e * x⁻¹ = e := by
    have h8 : x * (x * (x * e * x⁻¹) * x⁻¹) * x⁻¹ = x * e * x⁻¹ := by rw [h3]
    calc x * e * x⁻¹ = x * (x * (x * e * x⁻¹) * x⁻¹) * x⁻¹ := h8.symm
      _ = (x * x * x) * e * (x * x * x)⁻¹ := by group
      _ = e := by rw [hx3]; group
  rw [h7]
  exact hsq e he

theorem oneCenter_comm {Q : Subgroup H} :
    ∀ a ∈ oneCenter Q, ∀ b ∈ oneCenter Q, a * b = b * a := fun _ ha _ hb =>
  (mem_oneCenter.1 ha).2.2 _ (mem_oneCenter.1 hb).1

theorem oneCenter_normal {Q : Subgroup H} (hQ : Q.Normal) : (oneCenter Q).Normal :=
  ⟨fun _ he g => oneCenter_conj hQ he g⟩

def nQ (H : Type*) [Group H] (x : H) : Subgroup H :=
  nSub x (oneCenter (oQ H)) (oneCenter_normal inferInstance) oneCenter_comm

theorem mem_nQ {x n : H} : n ∈ nQ H x ↔ ∃ e ∈ oneCenter (oQ H), n = e * (x * e * x⁻¹) :=
  Iff.rfl

theorem nQ_le (x : H) : nQ H x ≤ oneCenter (oQ H) := nSub_le

theorem nQ_fix {x : H} (hx3 : x * x * x = 1) {n : H} (hn : n ∈ nQ H x)
    (hfix : x * n * x⁻¹ = n) : n = 1 :=
  nSub_fix hx3 (fun _ he => (mem_oneCenter.1 he).2.1) hn hfix

theorem Sig3.nQ_normal [Finite H] (h : Sig3 H S) {x : H} (hx : orderOf x = 3) :
    (nQ H x).Normal := by
  have hx3 := mul_mul_eq_one_of_orderOf hx
  have hQn : (oQ H).Normal := inferInstance
  refine normal_of_gen hx3 (h.gen hx) (nQ H x) ?_ ?_
  · intro s hs _ hk
    obtain ⟨e, he, rfl⟩ := mem_nQ.1 hk
    have he' : s * e * s⁻¹ ∈ oneCenter (oQ H) := oneCenter_conj hQn he s
    have hw : x * (s * e * s⁻¹) * x⁻¹ ∈ oneCenter (oQ H) := oneCenter_conj hQn he' x
    rcases h.conj_x_cases hx hs with ⟨q, hq, hsx⟩ | ⟨q, hq, hsx⟩
    · refine mem_nQ.2 ⟨s * e * s⁻¹, he', ?_⟩
      have hc : q * (x * (s * e * s⁻¹) * x⁻¹) = (x * (s * e * s⁻¹) * x⁻¹) * q :=
        ((mem_oneCenter.1 hw).2.2 q hq).symm
      calc s * (e * (x * e * x⁻¹)) * s⁻¹
          = (s * e * s⁻¹) * ((s * x * s⁻¹) * (s * e * s⁻¹) * (s * x * s⁻¹)⁻¹) := by group
        _ = (s * e * s⁻¹) * ((q * x) * (s * e * s⁻¹) * (q * x)⁻¹) := by rw [hsx]
        _ = (s * e * s⁻¹) * (q * (x * (s * e * s⁻¹) * x⁻¹) * q⁻¹) := by group
        _ = (s * e * s⁻¹) * (x * (s * e * s⁻¹) * x⁻¹) := by rw [hc]; group
    · have hw' : x⁻¹ * (s * e * s⁻¹) * x ∈ oneCenter (oQ H) := by
        simpa using oneCenter_conj hQn he' x⁻¹
      refine mem_nQ.2 ⟨x⁻¹ * (s * e * s⁻¹) * x, hw', ?_⟩
      have hc : q * (x⁻¹ * (s * e * s⁻¹) * x) = (x⁻¹ * (s * e * s⁻¹) * x) * q :=
        ((mem_oneCenter.1 hw').2.2 q hq).symm
      have hcomm := oneCenter_comm _ he' _ hw'
      calc s * (e * (x * e * x⁻¹)) * s⁻¹
          = (s * e * s⁻¹) * ((s * x * s⁻¹) * (s * e * s⁻¹) * (s * x * s⁻¹)⁻¹) := by group
        _ = (s * e * s⁻¹) * ((q * x⁻¹) * (s * e * s⁻¹) * (q * x⁻¹)⁻¹) := by rw [hsx]
        _ = (s * e * s⁻¹) * (q * (x⁻¹ * (s * e * s⁻¹) * x) * q⁻¹) := by group
        _ = (s * e * s⁻¹) * (x⁻¹ * (s * e * s⁻¹) * x) := by rw [hc]; group
        _ = (x⁻¹ * (s * e * s⁻¹) * x) * (s * e * s⁻¹) := hcomm
        _ = (x⁻¹ * (s * e * s⁻¹) * x) * (x * (x⁻¹ * (s * e * s⁻¹) * x) * x⁻¹) := by group
  · intro k hk
    obtain ⟨e, he, rfl⟩ := mem_nQ.1 hk
    have hw : x * e * x⁻¹ ∈ oneCenter (oQ H) := oneCenter_conj hQn he x
    exact mem_nQ.2 ⟨x * e * x⁻¹, hw, by group⟩

end CFSG.Quasithin.Fan86.Sigma3
