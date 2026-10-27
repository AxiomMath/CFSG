module

public import CFSG.Quasithin.Vol2.Asc94.HeJ9

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def InCore (L K : Subgroup G) (k : G) : Prop := k ∈ L ∧ ∀ l ∈ L, l⁻¹ * k * l ∈ K

theorem InCore.one (L K : Subgroup G) : InCore L K 1 :=
  ⟨one_mem _, fun l _ => by simpa using K.one_mem⟩

theorem InCore.mul {L K : Subgroup G} {x y : G} (hx : InCore L K x) (hy : InCore L K y) :
    InCore L K (x * y) :=
  ⟨L.mul_mem hx.1 hy.1, fun l hl => by
    have : l⁻¹ * (x * y) * l = (l⁻¹ * x * l) * (l⁻¹ * y * l) := by group
    rw [this]
    exact K.mul_mem (hx.2 l hl) (hy.2 l hl)⟩

theorem InCore.inv {L K : Subgroup G} {x : G} (hx : InCore L K x) : InCore L K x⁻¹ :=
  ⟨L.inv_mem hx.1, fun l hl => by
    have : l⁻¹ * x⁻¹ * l = (l⁻¹ * x * l)⁻¹ := by group
    rw [this]
    exact K.inv_mem (hx.2 l hl)⟩

theorem InCore.conj {L K : Subgroup G} {x l : G} (hx : InCore L K x) (hl : l ∈ L) :
    InCore L K (l⁻¹ * x * l) :=
  ⟨by simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hl) hx.1) hl, fun l' hl' => by
    have : l'⁻¹ * (l⁻¹ * x * l) * l' = (l * l')⁻¹ * x * (l * l') := by group
    rw [this]
    exact hx.2 _ (L.mul_mem hl hl')⟩

theorem InCore.mem_K {L K : Subgroup G} {x : G} (hx : InCore L K x) : x ∈ K := by
  simpa using hx.2 1 (one_mem _)

theorem gl2_cent_three : ∀ g h : GL2, g ^ 3 = 1 → g ≠ 1 → h.val * g.val = g.val * h.val →
    h ^ 3 = 1 := by
  set_option synthInstance.maxSize 1000 in
  set_option synthInstance.maxHeartbeats 200000 in
  decide +kernel

theorem v2_orbit : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ v₀ : V2, v₀ ≠ 0 → ∀ v : V2,
    v = 0 ∨ v = v₀ ∨ v = (g.val)ᵀ *ᵥ v₀ ∨ v = ((g⁻¹ : GL2).val)ᵀ *ᵥ v₀ := by
  decide +kernel

@[expose] def Lg (A : Subgroup G) (a b : G) : Subgroup G :=
  (normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G)

@[expose] def Kg (N : Subgroup G) (a b : G) : Subgroup G :=
  (N ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G)

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

include hD

theorem Data40.exists_D_rho (h : GL2) :
    ∃ d : N, (d : G) ∈ centralizer ({a} : Set G) ∧ (hD.hT.rho N hD.hK.norm d).1 = h := by
  obtain ⟨d, hd⟩ := hD.hT.rho_surjective hD.hK (h, gl2T h⁻¹)
  have hd1 : ((hD.hT.rho N hD.hK.norm d).1 : GL2).val = h.val := by rw [hd]
  have hd2 : ((hD.hT.rho N hD.hK.norm d).2 : GL2).val = (h⁻¹.val)ᵀ := by rw [hd]; rfl
  have hdN : (d : G) ∈ N := d.2
  have hdm : m ((d : G) * a * (d : G)⁻¹) = 1 := by
    rw [hD.hT.m_conj N hD.hK.norm d hD.ha, hD.ham, hd1, hd2, Matrix.transpose_transpose, mul_one]
    exact Units.mul_inv h
  have hda : (d : G) ∈ centralizer ({a} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (d : G) * a * (d : G)⁻¹ = a :=
      hD.hT.minj _ (hD.mem_Z_conj hdN hD.ha) _ hD.ha (by rw [hdm, hD.ham])
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  exact ⟨d, hda, by rw [hd]⟩

theorem Data40.exists_mul_of_mem_sup {j : G} (hj : j ∈ A ⊔ A') : ∃ a₁ ∈ A, ∃ a₂ ∈ A', j = a₁ * a₂ := by
  have hAA : ∀ y ∈ A', ∀ x ∈ A, y * x * y⁻¹ ∈ A := by
    intro y hy x hx
    obtain ⟨hz, -⟩ := hD.hT.comm x hx y hy
    have : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
    rw [this]
    exact A.mul_mem (A.inv_mem (Subgroup.mem_inf.1 hz).1) hx
  refine sup_induction (A := A) (A' := A') (P := fun j => ∃ a₁ ∈ A, ∃ a₂ ∈ A', j = a₁ * a₂)
    (fun x hx => ⟨x, hx, 1, A'.one_mem, by simp⟩) (fun x hx => ⟨1, A.one_mem, x, hx, by simp⟩)
    ⟨1, A.one_mem, 1, A'.one_mem, by simp⟩ ?_ ?_ hj
  · rintro _ _ - - ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    refine ⟨a₁ * (a₂ * b₁ * a₂⁻¹), A.mul_mem ha₁ (hAA a₂ ha₂ b₁ hb₁), a₂ * b₂, A'.mul_mem ha₂ hb₂, ?_⟩
    group
  · rintro _ - ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    refine ⟨a₂⁻¹ * a₁⁻¹ * a₂, ?_, a₂⁻¹, A'.inv_mem ha₂, ?_⟩
    · have := hAA a₂⁻¹ (A'.inv_mem ha₂) a₁⁻¹ (A.inv_mem ha₁)
      simpa using this
    · group

theorem Data40.rho2_eq {k : G} (hkN : k ∈ N) (hka : k ∈ centralizer ({a} : Set G)) :
    ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).2 : M2) =
      ((((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).1)⁻¹ : GL2) : M2)ᵀ := by
  have := hD.rho_D_inv (n := ⟨k, hkN⟩) hka
  rw [← this, Matrix.transpose_transpose]

section X

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)
  {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G))
  (hbm : m b = ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val)

include hxN hxa hx3 hb hbm

theorem Data40.Kg_le_Lg :
    (N ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G) ≤
      (normalizer (A : Set G) ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G) :=
  inf_le_inf_right _ (inf_le_inf_right _ hD.N_le_M)

theorem Data40.J_le_Kg :
    A ⊔ A' ≤ (N ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G) := by
  have hbZ : b ∈ A ⊓ A' := hb.1
  have haZ : a ∈ A ⊓ A' := hD.ha
  refine sup_le ?_ ?_
  · intro y hy
    refine ⟨⟨hD.hK.JN ((le_sup_left : A ≤ A ⊔ A') hy), ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.2 (hD.hK.Aab y hy a haZ.1)
    · exact mem_centralizer_singleton_iff.2 (hD.hK.Aab y hy b hbZ.1)
  · intro y hy
    refine ⟨⟨hD.hK.JN ((le_sup_right : A' ≤ A ⊔ A') hy), ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.2 (hD.hK.A'ab y hy a haZ.2)
    · exact mem_centralizer_singleton_iff.2 (hD.hK.A'ab y hy b hbZ.2)

theorem Data40.Kg_g_cube {k : G} (hkN : k ∈ N) (hka : k ∈ centralizer ({a} : Set G))
    (hkb : k ∈ centralizer ({b} : Set G)) :
    ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).1 : GL2) ^ 3 = 1 := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  set gk := ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).1 : GL2) with hgk
  have hbk : k * b * k⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.1 hkb
  have h1 : m (k * b * k⁻¹) = (gk : M2) * m b * ((gk⁻¹ : GL2) : M2) :=
    hD.m_conj_D (n := ⟨k, hkN⟩) hka hb.1
  rw [hbk, hbm] at h1
  have h2 : gk.val * g.val = g.val * gk.val := by
    calc gk.val * g.val = (gk.val * g.val * (gk⁻¹ : GL2).val) * gk.val := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = g.val * gk.val := by rw [← h1]
  exact gl2_cent_three g gk (hD.g_pow_three hxN hxa hx3) (hD.g_ne_one hxN hxa hx3) h2

theorem Data40.mem_J_of_g_one {k : G} (hkN : k ∈ N) (hka : k ∈ centralizer ({a} : Set G))
    (hk1 : (hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).1 = 1) : k ∈ A ⊔ A' := by
  have hρ := hD.rho_D (n := ⟨k, hkN⟩) hka
  rw [hk1] at hρ
  have h2 : ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).2 : M2) = 1 := by
    have : ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).2 : M2)ᵀ = 1 := by simpa using hρ
    simpa using congrArg Matrix.transpose this
  have hone : hD.hT.rho N hD.hK.norm ⟨k, hkN⟩ = 1 := Prod.ext hk1 (Units.ext h2)
  have hker : (⟨k, hkN⟩ : N) ∈ (hD.hT.rho N hD.hK.norm).ker := hone
  rw [hD.hT.ker_rho hD.hK, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem Data40.exists_Kg_rho (h : GL2)
    (hh : h.val * ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val =
      ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val * h.val) :
    ∃ (k : G) (hkN : k ∈ N), k ∈ centralizer ({a} : Set G) ∧ k ∈ centralizer ({b} : Set G) ∧
      (hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).1 = h := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  obtain ⟨d, hda, hd1⟩ := hD.exists_D_rho h
  refine ⟨d, d.2, hda, ?_, hd1⟩
  have hdm : m ((d : G) * b * (d : G)⁻¹) = m b := by
    rw [hD.m_conj_D (n := d) hda hb.1, hd1, hbm]
    calc h.val * g.val * (h⁻¹ : GL2).val = (g.val * h.val) * (h⁻¹ : GL2).val := by rw [hh]
      _ = g.val := by rw [mul_assoc, Units.mul_inv, mul_one]
  have h1 : (d : G) * b * (d : G)⁻¹ = b :=
    hD.hT.minj _ (hD.mem_Z_conj d.2 hb.1) _ hb.1 hdm
  rw [mem_centralizer_singleton_iff]
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem Data40.A_le_Kg : A ≤ Kg N a b := by
  intro y hy
  exact hD.J_le_Kg hxN hxa hx3 hb hbm ((le_sup_left : A ≤ A ⊔ A') hy)

theorem Data40.A_core {y : G} (hy : y ∈ A) : InCore (Lg A a b) (Kg N a b) y := by
  refine ⟨hD.Kg_le_Lg hxN hxa hx3 hb hbm (hD.A_le_Kg hxN hxa hx3 hb hbm hy), fun l hl => ?_⟩
  refine hD.A_le_Kg hxN hxa hx3 hb hbm ?_
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hl.1.1) y).1 hy
  simpa using this

theorem Data40.exists_core_w {j₀ : G} (hj₀A' : j₀ ∈ A')
    (hj₀ : InCore (Lg A a b) (Kg N a b) j₀) (hw : w j₀ ≠ 0) :
    ∀ v : V2, ∃ j ∈ A', InCore (Lg A a b) (Kg N a b) j ∧ w j = v := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  have hconj : ∀ (k : G) (hkN : k ∈ N), k ∈ centralizer ({a} : Set G) →
      k ∈ centralizer ({b} : Set G) →
      ∃ j ∈ A', InCore (Lg A a b) (Kg N a b) j ∧
        w j = ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).2 : M2) *ᵥ w j₀ := by
    intro k hkN hka hkb
    refine ⟨k * j₀ * k⁻¹, (hD.hK.norm k hkN).2 j₀ hj₀A', ?_,
      hD.hT.w_conj N hD.hK.norm ⟨k, hkN⟩ hj₀A'⟩
    have hkK : k ∈ Kg N a b := ⟨⟨hkN, hka⟩, hkb⟩
    have hkL : k⁻¹ ∈ Lg A a b := inv_mem (hD.Kg_le_Lg hxN hxa hx3 hb hbm hkK)
    have := hj₀.conj hkL
    simpa using this
  intro v
  rcases v2_orbit g (hD.g_pow_three hxN hxa hx3) (hD.g_ne_one hxN hxa hx3) (w j₀) hw v with
    h | h | h | h
  · exact ⟨1, A'.one_mem, InCore.one _ _, by rw [h]; exact hD.hT.cw.map_one⟩
  · exact ⟨j₀, hj₀A', hj₀, h.symm⟩
  · obtain ⟨k, hkN, hka, hkb, hk1⟩ := hD.exists_Kg_rho hxN hxa hx3 hb hbm g⁻¹
      (by rw [Units.inv_mul, Units.mul_inv])
    obtain ⟨j, hjA', hjc, hjw⟩ := hconj k hkN hka hkb
    refine ⟨j, hjA', hjc, ?_⟩
    rw [hjw, h, hD.rho2_eq hkN hka, hk1, inv_inv]
  · obtain ⟨k, hkN, hka, hkb, hk1⟩ := hD.exists_Kg_rho hxN hxa hx3 hb hbm g rfl
    obtain ⟨j, hjA', hjc, hjw⟩ := hconj k hkN hka hkb
    refine ⟨j, hjA', hjc, ?_⟩
    rw [hjw, h, hD.rho2_eq hkN hka, hk1]

theorem Data40.core_A'_w (hN : N = normalizer ((A ⊔ A' : Subgroup G) : Set G))
    (hLK : Nat.card ↥(Kg N a b) < Nat.card ↥(Lg A a b)) {j : G} (hjA' : j ∈ A')
    (hj : InCore (Lg A a b) (Kg N a b) j) : w j = 0 := by
  by_contra hw
  have hA'core : ∀ y ∈ A', InCore (Lg A a b) (Kg N a b) y := by
    intro y hy
    obtain ⟨j', hj'A', hj'c, hj'w⟩ := hD.exists_core_w hxN hxa hx3 hb hbm hjA' hj hw (w y)
    have hyj : y * j'⁻¹ ∈ A := hD.hT.cw.mul_inv_mem hy hj'A' hj'w.symm
    have : y = (y * j'⁻¹) * j' := by group
    rw [this]
    exact (hD.A_core hxN hxa hx3 hb hbm hyj).mul hj'c
  have hJcore : ∀ y ∈ A ⊔ A', InCore (Lg A a b) (Kg N a b) y := by
    intro y hy
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hD.exists_mul_of_mem_sup hy
    exact (hD.A_core hxN hxa hx3 hb hbm ha₁).mul (hA'core a₂ ha₂)
  have hconjJ : ∀ l ∈ Lg A a b, ∀ y ∈ A ⊔ A', l⁻¹ * y * l ∈ A ⊔ A' := by
    intro l hl y hy
    obtain ⟨⟨hkN, hka⟩, hkb⟩ := (hJcore y hy).2 l hl
    refine hD.mem_J_of_g_one hxN hxa hx3 hb hbm hkN hka ?_
    have hg3 := hD.Kg_g_cube hxN hxa hx3 hb hbm hkN hka hkb
    have hy256 : y ^ 256 = 1 := by
      have h := orderOf_dvd_natCard (⟨y, hy⟩ : ↥(A ⊔ A'))
      rw [hD.cardJ] at h
      have h2 : (⟨y, hy⟩ : ↥(A ⊔ A')) ^ 256 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
      simpa using congrArg Subtype.val h2
    have ht256 : (l⁻¹ * y * l) ^ 256 = 1 := by
      have : (l⁻¹ * y * l) ^ 256 = l⁻¹ * y ^ 256 * l := by
        simpa using conj_pow (a := l⁻¹) (b := y) (i := 256)
      rw [this, hy256]; group
    have hg256 : ((hD.hT.rho N hD.hK.norm ⟨l⁻¹ * y * l, hkN⟩).1 : GL2) ^ 256 = 1 := by
      have h1 : (⟨l⁻¹ * y * l, hkN⟩ : N) ^ 256 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact ht256)
      have := congrArg (fun r => r.1) (by rw [← map_pow, h1, map_one] :
        (hD.hT.rho N hD.hK.norm ⟨l⁻¹ * y * l, hkN⟩) ^ 256 = 1)
      simpa using this
    exact (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 256 3)).1 ⟨hg256, hg3⟩
  have hLleK : Lg A a b ≤ Kg N a b := by
    intro l hl
    have hlJ : l ∈ normalizer ((A ⊔ A' : Subgroup G) : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have := hconjJ l⁻¹ (inv_mem hl) y hy
      simpa using this
    rw [← hN] at hlJ
    exact ⟨⟨hlJ, hl.1.2⟩, hl.2⟩
  exact absurd (Subgroup.card_le_of_le hLleK) (not_le.2 hLK)

theorem Data40.core_le_A (hN : N = normalizer ((A ⊔ A' : Subgroup G) : Set G))
    (hLK : Nat.card ↥(Kg N a b) < Nat.card ↥(Lg A a b)) {k : G}
    (hk : InCore (Lg A a b) (Kg N a b) k) : k ∈ A := by
  obtain ⟨⟨hkN, hka⟩, hkb⟩ := hk.mem_K
  have hw1 : ((hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).2 : M2) = 1 := by
    rw [← mulVec_eq_self_iff]
    intro v
    obtain ⟨j, hjA', rfl⟩ := hD.hT.cw.surj v
    have hjL : j⁻¹ ∈ Lg A a b := inv_mem (hD.Kg_le_Lg hxN hxa hx3 hb hbm
      (hD.J_le_Kg hxN hxa hx3 hb hbm ((le_sup_right : A' ≤ A ⊔ A') hjA')))
    have hc : InCore (Lg A a b) (Kg N a b) (k * (j * k⁻¹ * j⁻¹)) := by
      refine hk.mul ?_
      have := hk.inv.conj hjL
      simpa using this
    have hcA' : k * (j * k⁻¹ * j⁻¹) ∈ A' := by
      have h1 : k * j * k⁻¹ ∈ A' := (hD.hK.norm k hkN).2 j hjA'
      have : k * (j * k⁻¹ * j⁻¹) = (k * j * k⁻¹) * j⁻¹ := by group
      rw [this]
      exact A'.mul_mem h1 (A'.inv_mem hjA')
    have hw0 := hD.core_A'_w hxN hxa hx3 hb hbm hN hLK hcA' hc
    have hcj : (k * (j * k⁻¹ * j⁻¹)) * j = k * j * k⁻¹ := by group
    have h2 : w (k * j * k⁻¹) = w j := by
      rw [← hcj, hD.hT.cw.mul _ hcA' j hjA', hw0, zero_add]
    rw [← hD.hT.w_conj N hD.hK.norm ⟨k, hkN⟩ hjA']
    exact h2
  have hg1 : (hD.hT.rho N hD.hK.norm ⟨k, hkN⟩).1 = 1 := by
    have hρ := hD.rho_D (n := ⟨k, hkN⟩) hka
    rw [hw1, Matrix.transpose_one, mul_one] at hρ
    exact Units.ext hρ
  have hkJ : k ∈ A ⊔ A' := hD.mem_J_of_g_one hxN hxa hx3 hb hbm hkN hka hg1
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hD.exists_mul_of_mem_sup hkJ
  have hcore2 : InCore (Lg A a b) (Kg N a b) a₂ := by
    have := (hD.A_core hxN hxa hx3 hb hbm (A.inv_mem ha₁)).mul hk
    simpa using this
  have hw0 := hD.core_A'_w hxN hxa hx3 hb hbm hN hLK ha₂ hcore2
  exact A.mul_mem ha₁ ((hD.hT.cw.zero a₂ ha₂).1 hw0)

end X

end D40

end CFSG.Quasithin.A94.HeJ
