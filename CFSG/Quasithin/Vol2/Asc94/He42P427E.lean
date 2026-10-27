module

public import CFSG.Quasithin.Vol2.Asc94.He42P427D

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem p427_a_ne_one (T : HeSetup G) : T.a ≠ 1 := by
  intro h
  have := T.hD.ham
  rw [h, T.hD.hT.m_one] at this
  exact absurd this (by decide)

theorem p427_cover_J (T : HeSetup G) (hB : T.BaseFacts) (hSp : T.StepSpread)
    {j : G} (hj : j ∈ T.J) (hj2 : j * j = 1) (hjB : j ∉ T.B) :
    ∃ h ∈ T.L, h⁻¹ * j * h ∈ T.Z := by
  rcases p427_invol_J T hB hj hj2 with hA | hA'
  · obtain ⟨h, hh, hhZ⟩ := p427_cover_gen T.A T.Z T.B T.K T.L1 hB.Z_le_A hB.B_le_Z hB.card_A
      hB.card_Z hB.card_B hB.L1_le_normalizer
      (fun l hl b hb => (mem_centralizer_iff.1 (hB.L1_le_centralizer hl) b hb).symm)
      hB.K_le_L1 hB.relIndex_K_L1 hSp.1 j hA hjB
    exact ⟨h, Subgroup.mem_sup_left hh, hhZ⟩
  · obtain ⟨h, hh, hhZ⟩ := p427_cover_gen T.A' T.Z T.B T.K T.L2 hB.Z_le_A' hB.B_le_Z hB.card_A'
      hB.card_Z hB.card_B hB.L2_le_normalizer
      (fun l hl b hb => (mem_centralizer_iff.1 (hB.L2_le_centralizer hl) b hb).symm)
      hB.K_le_L2 hB.relIndex_K_L2 hSp.2 j hA' hjB
    exact ⟨h, Subgroup.mem_sup_right hh, hhZ⟩

theorem p427_isol_L (T : HeSetup G) (hB : T.BaseFacts)
    (hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L)
    (hLcard : Nat.card T.L = 80640) {z : G} (P : P427 T z)
    {b : G} (hbB : b ∈ T.B) (hb1 : b ≠ 1) (hba : b ≠ T.a)
    {x : G} (hx : x ∈ centralizer ({T.a} : Set G))
    (hcN : x * b * x⁻¹ ∈ normalizer (T.B : Set G)) : x * b * x⁻¹ ∈ T.L := by
  by_contra hcL
  have haB : T.a ∈ T.B := T.hD.a_mem_B T.hxN T.hxa T.hx3
  have haZ : T.a ∈ T.Z := T.hD.ha
  have hbZ : b ∈ T.Z := hB.B_le_Z hbB
  have hb2 : b * b = 1 := hB.A_sq b (hB.Z_le_A hbZ)
  have hzZ : z ∈ T.Z := P.hzZ
  have hza : z * T.a = T.a * z :=
    mem_centralizer_singleton_iff.1 (mem_centralizer_singleton_iff.2
      (hB.A_comm z (hB.Z_le_A hzZ) T.a (hB.Z_le_A haZ)))
  have hbM : b ∈ centralizer ({T.a} : Set G) :=
    mem_centralizer_singleton_iff.2 (hB.A_comm b (hB.Z_le_A hbZ) T.a (hB.Z_le_A haZ))
  have hLM : T.L ≤ centralizer ({T.a} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (p427_L_le_centB T hB hl) T.a haB).symm
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * b * x⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hcN hcL
  have hcKB : c ∈ KB T := by
    refine Subgroup.mem_inf.2 ⟨?_, hcN⟩
    rw [hcdef]
    exact (centralizer ({T.a} : Set G)).mul_mem ((centralizer ({T.a} : Set G)).mul_mem hx hbM)
      ((centralizer ({T.a} : Set G)).inv_mem hx)
  have hc2 : c * c = 1 := by
    rw [hcdef]
    calc x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hKB := p427_KB_card T hB hL hLcard P.hzZ haZ P.hS
  obtain ⟨k, hk, hkS⟩ := p427_conj_KB T hB P.hS
    (p427_S_le_KB T P.hzZ haZ P.hS haB (p427_a_ne_one T) hB) hKB hcKB hc2
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : G, c₁ = k⁻¹ * c * k := ⟨_, rfl⟩
  rw [← hc₁def] at hkS
  obtain ⟨m₁, hm₁def⟩ : ∃ m₁ : G, m₁ = k⁻¹ * x := ⟨_, rfl⟩
  have hkM : k ∈ centralizer ({T.a} : Set G) := (Subgroup.mem_inf.1 hk).1
  have hm₁M : m₁ ∈ centralizer ({T.a} : Set G) := by
    rw [hm₁def]
    exact (centralizer ({T.a} : Set G)).mul_mem ((centralizer ({T.a} : Set G)).inv_mem hkM) hx
  have hm₁b : m₁ * b * m₁⁻¹ = c₁ := by
    rw [hm₁def, hc₁def, hcdef]
    group
  have hc₁2 : c₁ * c₁ = 1 := by
    rw [hc₁def]
    calc k⁻¹ * c * k * (k⁻¹ * c * k) = k⁻¹ * (c * c) * k := by group
      _ = 1 := by rw [hc2]; group
  have hc₁S : c₁ ∈ centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) := hkS
  have hzc₁ : z * c₁ = c₁ * z := (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc₁S).1).symm
  have hc₁L : c₁ ∉ T.L := by
    intro hc₁L'
    apply hcL
    apply hL
    intro y hy
    have hk' : k⁻¹ * y * k ∈ T.B := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (Subgroup.mem_inf.1 hk).2) y).1 hy
      simpa using this
    have hcomm := mem_centralizer_iff.1 (p427_L_le_centB T hB hc₁L') _ hk'
    have e1 : c = k * c₁ * k⁻¹ := by rw [hc₁def]; group
    rw [e1]
    calc k * c₁ * k⁻¹ * y = k * (c₁ * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * c₁) * k⁻¹ := by rw [hcomm]
      _ = y * (k * c₁ * k⁻¹) := by group
  have hc₁J : c₁ ∉ T.J := fun h => hc₁L (p427_J_le_L T hB h)
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = m₁⁻¹ * z * m₁ := ⟨_, rfl⟩
  have hmz : m₁ * w * m₁⁻¹ = z := by rw [hwdef]; group
  have hzcomm : ∀ y ∈ T.B, w * y = y * w := by
    intro y hy
    have hy' : z * (m₁ * y * m₁⁻¹) = (m₁ * y * m₁⁻¹) * z := by
      rcases T.hD.B_elems T.hxN T.hxa T.hx3 hbB hb1 hba y hy with rfl | rfl | rfl | rfl
      · simp
      · have ha' : m₁ * T.a * m₁⁻¹ = T.a := by
          rw [mem_centralizer_singleton_iff.1 hm₁M]
          group
        rw [ha', hza]
      · rw [hm₁b, hzc₁]
      · have hab : m₁ * (T.a * b) * m₁⁻¹ = T.a * c₁ := by
          have ha' : m₁ * T.a * m₁⁻¹ = T.a := by
            rw [mem_centralizer_singleton_iff.1 hm₁M]
            group
          rw [show m₁ * (T.a * b) * m₁⁻¹ = (m₁ * T.a * m₁⁻¹) * (m₁ * b * m₁⁻¹) by group,
            ha', hm₁b]
        rw [hab]
        calc z * (T.a * c₁) = (z * T.a) * c₁ := by group
          _ = (T.a * z) * c₁ := by rw [hza]
          _ = T.a * (z * c₁) := by group
          _ = T.a * (c₁ * z) := by rw [hzc₁]
          _ = (T.a * c₁) * z := by group
    calc w * y = m₁⁻¹ * (z * (m₁ * y * m₁⁻¹)) * m₁ := by rw [hwdef]; group
      _ = m₁⁻¹ * ((m₁ * y * m₁⁻¹) * z) * m₁ := by rw [hy']
      _ = y * w := by rw [hwdef]; group
  have hwL : w ∈ T.L := hL w hzcomm
  have hw2 : w * w = 1 := by
    rw [hwdef]
    calc m₁⁻¹ * z * m₁ * (m₁⁻¹ * z * m₁) = m₁⁻¹ * (z * z) * m₁ := by group
      _ = 1 := by rw [P.hz2]; group
  have hcardL := p427_card_cent_L T hB hLcard hwL hw2
  have ha' : m₁ * T.a * m₁⁻¹ = T.a := by
    rw [mem_centralizer_singleton_iff.1 hm₁M]
    group
  have hinj : Nat.card ↥(centralizer ({w} : Set G) ⊓ T.L) ≤
      Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ⊓
        centralizer ({c₁} : Set G)) := by
    let φ : ↥(centralizer ({w} : Set G) ⊓ T.L) → ↥(centralizer ({z} : Set G) ⊓
        centralizer ({T.a} : Set G) ⊓ centralizer ({c₁} : Set G)) := fun y =>
      ⟨m₁ * (y : G) * m₁⁻¹, by
        obtain ⟨hyw, hyL⟩ := Subgroup.mem_inf.1 y.2
        have hyw' : (y : G) * w = w * (y : G) := mem_centralizer_singleton_iff.1 hyw
        have hyb : ∀ b' ∈ T.B, (y : G) * b' = b' * (y : G) :=
          fun b' hb' => (mem_centralizer_iff.1 (p427_L_le_centB T hB hyL) b' hb').symm
        have hyaM : (y : G) * T.a = T.a * (y : G) :=
          mem_centralizer_singleton_iff.1 (hLM hyL)
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
        · rw [mem_centralizer_singleton_iff]
          calc (m₁ * (y : G) * m₁⁻¹) * z = (m₁ * (y : G) * m₁⁻¹) * (m₁ * w * m₁⁻¹) := by rw [hmz]
            _ = m₁ * ((y : G) * w) * m₁⁻¹ := by group
            _ = m₁ * (w * (y : G)) * m₁⁻¹ := by rw [hyw']
            _ = (m₁ * w * m₁⁻¹) * (m₁ * (y : G) * m₁⁻¹) := by group
            _ = z * (m₁ * (y : G) * m₁⁻¹) := by rw [hmz]
        · rw [mem_centralizer_singleton_iff]
          calc (m₁ * (y : G) * m₁⁻¹) * T.a = (m₁ * (y : G) * m₁⁻¹) * (m₁ * T.a * m₁⁻¹) := by rw [ha']
            _ = m₁ * ((y : G) * T.a) * m₁⁻¹ := by group
            _ = m₁ * (T.a * (y : G)) * m₁⁻¹ := by rw [hyaM]
            _ = (m₁ * T.a * m₁⁻¹) * (m₁ * (y : G) * m₁⁻¹) := by group
            _ = T.a * (m₁ * (y : G) * m₁⁻¹) := by rw [ha']
        · rw [mem_centralizer_singleton_iff]
          calc (m₁ * (y : G) * m₁⁻¹) * c₁ = (m₁ * (y : G) * m₁⁻¹) * (m₁ * b * m₁⁻¹) := by rw [hm₁b]
            _ = m₁ * ((y : G) * b) * m₁⁻¹ := by group
            _ = m₁ * (b * (y : G)) * m₁⁻¹ := by rw [hyb b hbB]
            _ = (m₁ * b * m₁⁻¹) * (m₁ * (y : G) * m₁⁻¹) := by group
            _ = c₁ * (m₁ * (y : G) * m₁⁻¹) := by rw [hm₁b]⟩
    have hφinj : Function.Injective φ := by
      intro y y' h
      have h' : m₁ * (y : G) * m₁⁻¹ = m₁ * (y' : G) * m₁⁻¹ := congrArg Subtype.val h
      apply Subtype.ext
      have := congrArg (fun t => m₁⁻¹ * t * m₁) h'
      simpa using this
    exact Nat.card_le_card_of_injective φ hφinj
  have hS3' := P.hS3 c₁ hc₁S hc₁2 hc₁J
  omega

theorem p427_isol (T : HeSetup G) (hB : T.BaseFacts)
    (hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L)
    (hLcard : Nat.card T.L = 80640) {z : G} (P : P427 T z)
    {b : G} (hbB : b ∈ T.B) (hb1 : b ≠ 1) (hba : b ≠ T.a) (hbm : T.m b = T.g.val)
    {x : G} (hx : x ∈ centralizer ({T.a} : Set G))
    (hcN : x * b * x⁻¹ ∈ normalizer (T.B : Set G)) : x * b * x⁻¹ ∈ T.B := by
  have hcL := p427_isol_L T hB hL hLcard P hbB hb1 hba hx hcN
  by_contra hcB
  have haB : T.a ∈ T.B := T.hD.a_mem_B T.hxN T.hxa T.hx3
  have haZ : T.a ∈ T.Z := T.hD.ha
  have hbZ : b ∈ T.Z := hB.B_le_Z hbB
  have hb2 : b * b = 1 := hB.A_sq b (hB.Z_le_A hbZ)
  have hbM : b ∈ centralizer ({T.a} : Set G) :=
    mem_centralizer_singleton_iff.2 (hB.A_comm b (hB.Z_le_A hbZ) T.a (hB.Z_le_A haZ))
  have hLM : T.L ≤ centralizer ({T.a} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (p427_L_le_centB T hB hl) T.a haB).symm
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * b * x⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hcN hcL hcB
  have hc2 : c * c = 1 := by
    rw [hcdef]
    calc x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  obtain ⟨l, hl, hlJ⟩ := p427_conj_L_J T hB hLcard hcL hc2
  obtain ⟨cJ, hcJdef⟩ : ∃ cJ : G, cJ = l⁻¹ * c * l := ⟨_, rfl⟩
  rw [← hcJdef] at hlJ
  have hcJB : cJ ∉ T.B := by
    intro hcJB'
    apply hcB
    have e : c = cJ := by
      have hlc := mem_centralizer_iff.1 (p427_L_le_centB T hB hl) cJ hcJB'
      calc c = l * cJ * l⁻¹ := by rw [hcJdef]; group
        _ = cJ := by rw [← hlc]; group
    rw [e]
    exact hcJB'
  have hcJ2 : cJ * cJ = 1 := by
    rw [hcJdef]
    calc l⁻¹ * c * l * (l⁻¹ * c * l) = l⁻¹ * (c * c) * l := by group
      _ = 1 := by rw [hc2]; group
  obtain ⟨h, hh, hhZ⟩ := p427_cover_J T hB P.hSp hlJ hcJ2 hcJB
  obtain ⟨c₂, hc₂def⟩ : ∃ c₂ : G, c₂ = h⁻¹ * cJ * h := ⟨_, rfl⟩
  rw [← hc₂def] at hhZ
  have hc₂B : c₂ ∉ T.B := by
    intro hc₂B'
    apply hcJB
    have hhc := mem_centralizer_iff.1 (p427_L_le_centB T hB hh) c₂ hc₂B'
    have e : cJ = c₂ := by
      calc cJ = h * (h⁻¹ * cJ * h) * h⁻¹ := by group
        _ = h * c₂ * h⁻¹ := by rw [hc₂def]
        _ = c₂ * (h * h⁻¹) := by rw [← hhc]; group
        _ = c₂ := by group
    rw [e]
    exact hc₂B'
  obtain ⟨m', hm'def⟩ : ∃ m' : G, m' = h⁻¹ * l⁻¹ * x := ⟨_, rfl⟩
  have hm'M : m' ∈ centralizer ({T.a} : Set G) := by
    rw [hm'def]
    exact (centralizer ({T.a} : Set G)).mul_mem
      ((centralizer ({T.a} : Set G)).mul_mem ((centralizer ({T.a} : Set G)).inv_mem (hLM hh))
        ((centralizer ({T.a} : Set G)).inv_mem (hLM hl))) hx
  have hm'b : m' * b * m'⁻¹ = c₂ := by
    rw [hm'def, hc₂def, hcJdef, hcdef]
    group
  have hc₂Z : c₂ ∈ T.Z := hhZ
  have hg3 : T.g ^ 3 = 1 := T.hD.g_pow_three T.hxN T.hxa T.hx3
  have hg1 : T.g ≠ 1 := T.hD.g_ne_one T.hxN T.hxa T.hx3
  have hgdet : (T.g.val).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit T.g)).ne_zero
  have hbdet : (T.m b).det ≠ 0 := by rw [hbm]; exact hgdet
  have hm'inv : (m'⁻¹)⁻¹ = m' := inv_inv m'
  have hc₂det : (T.m c₂).det ≠ 0 :=
    p427_det_conj T P.hfus (g := m'⁻¹) hbZ hc₂Z (by rw [hm'inv, hm'b]) hbdet
  have hbaZ : b * T.a ∈ T.Z := T.Z.mul_mem hbZ haZ
  have hbadet : (T.m (b * T.a)).det ≠ 0 := by
    rw [T.hD.hT.mmul b hbZ T.a haZ, hbm, T.hD.ham]
    exact p427_fin_g1 T.g hg3 hg1
  have hc₂aZ : c₂ * T.a ∈ T.Z := T.Z.mul_mem hc₂Z haZ
  have hm'a : m' * T.a * m'⁻¹ = T.a := by
    rw [mem_centralizer_singleton_iff.1 hm'M]
    group
  have hc₂adet : (T.m (c₂ * T.a)).det ≠ 0 := by
    apply p427_det_conj T P.hfus (g := m'⁻¹) hbaZ hc₂aZ _ hbadet
    rw [hm'inv]
    calc m' * (b * T.a) * m'⁻¹ = (m' * b * m'⁻¹) * (m' * T.a * m'⁻¹) := by group
      _ = c₂ * T.a := by rw [hm'b, hm'a]
  have hdet1 : (T.m c₂ + 1).det ≠ 0 := by
    have h := T.hD.hT.mmul c₂ hc₂Z T.a haZ
    rw [T.hD.ham] at h
    rw [← h]
    exact hc₂adet
  have hcomm := p427_fin_comm T.g hg3 hg1 (T.m c₂) hc₂det hdet1
  exact hc₂B ((T.hD.mem_B_iff T.hxN T.hxa T.hx3).2 ⟨hc₂Z, hcomm⟩)

end CFSG.Quasithin.A94.He42
