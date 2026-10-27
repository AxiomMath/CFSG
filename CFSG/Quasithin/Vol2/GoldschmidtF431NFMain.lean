module

public import CFSG.Quasithin.Vol2.GoldschmidtF431NFSpecial
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.F431.NF

open CFSG.QuasithinUnique
open scoped commutatorElement

variable {M : Type*} [Group M]

structure NFDatum (S Q Z M₁ A B : Subgroup M) (z v : M) (q n : ℕ) : Prop where
  sylow : IsSylowTwoOf S ⊤
  cent_le : ∀ x ∈ Z, x ≠ 1 → Subgroup.centralizer ({x} : Set M) ≤ M₁
  Z_le_Q : Z ≤ Q
  Q_le_S : Q ≤ S
  Q_norm : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q
  Z_central : ∀ x ∈ Z, ∀ s ∈ S, s * x = x * s
  Z_exp : ∀ x ∈ Z, x * x = 1
  card_Z : Nat.card Z = q
  z_mem : z ∈ Z
  z_ne : z ≠ 1
  Q_comm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z
  Q_sq : ∀ x ∈ Q, x * x ∈ Z
  card_Q : Nat.card Q = q ^ (2 * n + 1)
  card_S : Nat.card S = q ^ (3 * n)
  S_comm : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ Q
  elem_abelian : ∀ E : Subgroup M, E ≤ Q → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ q ^ (n + 1)
  M₁_Z : ∀ y ∈ M₁, ∀ x ∈ Z, y * x * y⁻¹ ∈ Z
  M₁_Q : ∀ y ∈ M₁, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q
  M₁_trans : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ 1 → y ≠ 1 → ∃ m ∈ M₁, m * x * m⁻¹ = y
  A_conj : ∃ r : M, A = cj r Z
  B_conj : ∃ s : M, B = cj s Z
  A_le : A ≤ Q
  B_le : B ≤ Q
  Z_le_comm : Z ≤ ⁅A, B⁆
  v_mem : v ∈ Q
  v_not_mem : v ∉ Z
  v_comm_A : ∀ a ∈ A, a * v = v * a
  v_comm_B : ∀ b ∈ B, b * v = v * b
  v_not_cent : ∀ y ∈ M₁, ∃ s ∈ S, ⁅s, y * v * y⁻¹⁆ ∉ Z

theorem isPGroup_cj {S : Subgroup M} (hS : IsPGroup 2 S) (c : M) : IsPGroup 2 (cj c S) :=
  hS.of_equiv (Subgroup.equivMapOfInjective S (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective)

theorem index_cj (c : M) (S : Subgroup M) : (cj c S).index = S.index :=
  Subgroup.index_map_equiv (H := S) (MulAut.conj c)

theorem not_two_dvd_subgroupOf_index {T C : Subgroup M} (hTC : T ≤ C) (h : ¬ 2 ∣ T.index) :
    ¬ 2 ∣ (T.subgroupOf C).index :=
  fun h2 => h (h2.trans (Subgroup.relIndex_dvd_index_of_le hTC))

theorem not_isConj_of_nfDatum [Finite M] {S Q Z M₁ A B : Subgroup M} {z v : M} {q n : ℕ}
    (D : NFDatum S Q Z M₁ A B z v q n) : ¬ IsConj z v := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨r, rfl⟩ := D.A_conj
  obtain ⟨s, rfl⟩ := D.B_conj
  have hzZ := D.z_mem
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    (D.Z_central x hx y (D.Q_le_S (D.Z_le_Q hy))).symm
  have hTI : IsTI Z := isTI_of_cent_le D.M₁_Z D.cent_le D.M₁_trans
  have hS2 : IsPGroup 2 S := D.sylow.2.1
  have hSidx : ¬ 2 ∣ S.index := by
    have h := D.sylow.2.2
    have e : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rwa [e] at h
  have hvV : v ∈ cj g Z := by
    rw [mem_cj, ← hg]
    have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [this]
    exact hzZ
  have hv1 : v ≠ 1 := by
    intro h
    apply D.v_not_mem
    rw [h]
    exact Z.one_mem
  have hAV : ∀ x ∈ cj r Z, ∀ y ∈ cj g Z, x * y = y * x :=
    commute_of_isTI hTI D.Z_exp hZcomm hvV hv1 D.v_comm_A
  have hBV : ∀ x ∈ cj s Z, ∀ y ∈ cj g Z, x * y = y * x :=
    commute_of_isTI hTI D.Z_exp hZcomm hvV hv1 D.v_comm_B
  have hUV : cj r Z ⊔ cj s Z ≤ Subgroup.centralizer (cj g Z : Set M) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hAV x hx y hy).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hBV x hx y hy).symm
  have hgS : cj g S ≤ Subgroup.centralizer (cj g Z : Set M) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hs0 : g⁻¹ * t * g ∈ S := mem_cj.mp ht
    have hw : g⁻¹ * h * g ∈ Z := mem_cj.mp hh
    have e := D.Z_central _ hw _ hs0
    calc h * t = g * ((g⁻¹ * h * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * (g⁻¹ * h * g)) * g⁻¹ := by rw [← e]
      _ = t * h := by group
  have hAB2 : IsPGroup 2 ↥(cj r Z ⊔ cj s Z : Subgroup M) :=
    hS2.to_le (sup_le (D.A_le.trans D.Q_le_S) (D.B_le.trans D.Q_le_S))
  obtain ⟨y, hyC, hy⟩ := exists_conj_le_of_isPGroup (C := Subgroup.centralizer (cj g Z : Set M))
    (T := cj g S) hgS (isPGroup_cj hS2 g)
    (not_two_dvd_subgroupOf_index hgS (by rw [index_cj]; exact hSidx)) hUV hAB2
  have hyv : v * y = y * v := (Subgroup.mem_centralizer_iff.mp hyC) v hvV
  have hZ1 : ∀ t ∈ Z, (g⁻¹ * y) * t * (g⁻¹ * y)⁻¹ ∈ Q := by
    have hle : ⁅cj r Z, cj s Z⁆ ≤ Q.comap (MulAut.conj (g⁻¹ * y)).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      have ha' : (g⁻¹ * y) * a * (g⁻¹ * y)⁻¹ ∈ S := by
        have := mem_cj.mp (hy a (Subgroup.mem_sup_left ha))
        have e : g⁻¹ * (y * a * y⁻¹) * g = (g⁻¹ * y) * a * (g⁻¹ * y)⁻¹ := by group
        rwa [e] at this
      have hb' : (g⁻¹ * y) * b * (g⁻¹ * y)⁻¹ ∈ S := by
        have := mem_cj.mp (hy b (Subgroup.mem_sup_right hb))
        have e : g⁻¹ * (y * b * y⁻¹) * g = (g⁻¹ * y) * b * (g⁻¹ * y)⁻¹ := by group
        rwa [e] at this
      have h := D.S_comm _ ha' _ hb'
      have e : ⁅(g⁻¹ * y) * a * (g⁻¹ * y)⁻¹, (g⁻¹ * y) * b * (g⁻¹ * y)⁻¹⁆ =
          (g⁻¹ * y) * ⁅a, b⁆ * (g⁻¹ * y)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e] at h
      exact h
    intro t ht
    exact hle (D.Z_le_comm ht)
  set g₁ : M := y⁻¹ * g with hg₁
  have hg₁z : g₁ * z * g₁⁻¹ = v := by
    calc g₁ * z * g₁⁻¹ = y⁻¹ * (g * z * g⁻¹) * y := by rw [hg₁]; group
      _ = y⁻¹ * v * y := by rw [hg]
      _ = v := by
        calc y⁻¹ * v * y = y⁻¹ * (v * y) := by group
          _ = y⁻¹ * (y * v) := by rw [hyv]
          _ = v := by group
  have hZ₁ : ∀ t ∈ Z, g₁⁻¹ * t * g₁ ∈ Q := by
    intro t ht
    have h := hZ1 t ht
    have e : (g⁻¹ * y) * t * (g⁻¹ * y)⁻¹ = g₁⁻¹ * t * g₁ := by rw [hg₁]; group
    rwa [e] at h
  clear_value g₁
  set x : M := g₁⁻¹ * z * g₁ with hx
  have hxQ : x ∈ Q := hZ₁ z hzZ
  have hq : 0 < q := by
    rw [← D.card_Z]
    exact Nat.card_pos
  have hR₀card : q ^ (2 * n) ≤ Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set M) : Subgroup M) := by
    have h := card_le_card_inf_centralizer_mul (Z := Z) D.Z_le_Q
      (fun z' hz' y hy => D.Z_central z' hz' y (D.Q_le_S hy)) D.Q_comm hxQ
    rw [D.card_Q, D.card_Z, pow_succ] at h
    exact Nat.le_of_mul_le_mul_right h hq
  set R₀ : Subgroup M := cj g₁ (Q ⊓ Subgroup.centralizer ({x} : Set M)) with hR₀
  have hR₀le : R₀ ≤ cj g₁ Q := Subgroup.map_mono inf_le_left
  have hR₀cent : R₀ ≤ Subgroup.centralizer ({z} : Set M) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have ht' := mem_cj.mp ht
    have hc := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht').2) x (Set.mem_singleton x)
    have hzx : z = g₁ * x * g₁⁻¹ := by rw [hx]; group
    calc z * t = g₁ * (x * (g₁⁻¹ * t * g₁)) * g₁⁻¹ := by rw [hzx, hx]; group
      _ = g₁ * ((g₁⁻¹ * t * g₁) * x) * g₁⁻¹ := by rw [hc]
      _ = t * z := by rw [hzx, hx]; group
  have hR₀2 : IsPGroup 2 R₀ := (isPGroup_cj hS2 g₁).to_le
    ((Subgroup.map_mono (inf_le_left.trans D.Q_le_S) : R₀ ≤ cj g₁ S))
  have hSC : S ≤ Subgroup.centralizer ({z} : Set M) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (D.Z_central z hzZ t ht).symm
  obtain ⟨y₂, hy₂C, hy₂⟩ := exists_conj_le_of_isPGroup (C := Subgroup.centralizer ({z} : Set M))
    (T := S) hSC hS2 (not_two_dvd_subgroupOf_index hSC hSidx) hR₀cent hR₀2
  have hy₂z : y₂ * z = z * y₂ := by
    have := (Subgroup.mem_centralizer_iff.mp hy₂C) z (Set.mem_singleton z)
    exact this.symm
  have hy₂M : y₂ ∈ M₁ := D.cent_le z hzZ D.z_ne hy₂C
  set R₂ : Subgroup M := cj y₂ R₀ with hR₂
  have hR₂S : R₂ ≤ S := by
    intro t ht
    have h := hy₂ _ (mem_cj.mp ht)
    have e : y₂ * (y₂⁻¹ * t * y₂) * y₂⁻¹ = t := by group
    rwa [e] at h
  have hR₂card : q ^ (2 * n) ≤ Nat.card R₂ := by
    rw [hR₂, card_cj, hR₀, card_cj]
    exact hR₀card
  have hR₂le : R₂ ≤ cj (y₂ * g₁) Q := by
    intro t ht
    have h1 : y₂⁻¹ * t * y₂ ∈ R₀ := mem_cj.mp ht
    have h2 := mem_cj.mp (hR₀le h1)
    rw [mem_cj]
    have e : (y₂ * g₁)⁻¹ * t * (y₂ * g₁) = g₁⁻¹ * (y₂⁻¹ * t * y₂) * g₁ := by group
    rwa [e]
  set v₂ : M := y₂ * v * y₂⁻¹ with hv₂
  have hv₂c : (y₂ * g₁) * z * (y₂ * g₁)⁻¹ = v₂ := by
    calc (y₂ * g₁) * z * (y₂ * g₁)⁻¹ = y₂ * (g₁ * z * g₁⁻¹) * y₂⁻¹ := by group
      _ = v₂ := by rw [hg₁z]
  have hv₂Q : v₂ ∈ Q := D.M₁_Q y₂ hy₂M v D.v_mem
  have hv₂Z : v₂ ∉ Z := by
    intro h
    apply D.v_not_mem
    have := D.M₁_Z y₂⁻¹ (M₁.inv_mem hy₂M) _ h
    have e : y₂⁻¹ * v₂ * y₂⁻¹⁻¹ = v := by rw [hv₂]; group
    rwa [e] at this
  have hR₂v : ∀ t ∈ R₂, t * v₂ = v₂ * t := by
    intro t ht
    have h1 := mem_cj.mp (hR₂le ht)
    have hc := D.Z_central z hzZ _ (D.Q_le_S h1)
    calc t * v₂ = (y₂ * g₁) * ((y₂ * g₁)⁻¹ * t * (y₂ * g₁) * z) * (y₂ * g₁)⁻¹ := by
          rw [← hv₂c]; group
      _ = (y₂ * g₁) * (z * ((y₂ * g₁)⁻¹ * t * (y₂ * g₁))) * (y₂ * g₁)⁻¹ := by rw [hc]
      _ = v₂ * t := by rw [← hv₂c]; group
  have hZinf : Z ⊓ cj (y₂ * g₁) Z = ⊥ := by
    by_contra h
    have h2 := hTI _ h
    apply hv₂Z
    have : v₂ ∈ cj (y₂ * g₁) Z := by
      rw [mem_cj, ← hv₂c]
      have e : (y₂ * g₁)⁻¹ * ((y₂ * g₁) * z * (y₂ * g₁)⁻¹) * (y₂ * g₁) = z := by group
      rw [e]
      exact hzZ
    rwa [h2] at this
  obtain ⟨hsq, hco⟩ := inf_cj_elemAbelian D.Q_comm D.Q_sq hZinf
  have hEmem : ∀ t ∈ R₂ ⊓ Q, t ∈ Q ⊓ cj (y₂ * g₁) Q := fun t ht =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ht).2, hR₂le (Subgroup.mem_inf.mp ht).1⟩
  have hE : Nat.card (R₂ ⊓ Q : Subgroup M) ≤ q ^ (n + 1) :=
    D.elem_abelian _ inf_le_right (fun t ht => hsq t (hEmem t ht))
      (fun t ht t' ht' => hco t (hEmem t ht) t' (hEmem t' ht'))
  have hSnorm : S ≤ Subgroup.normalizer (Q : Set M) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact D.Q_norm t ht h hh
    · intro hh
      have := D.Q_norm t⁻¹ (S.inv_mem ht) _ hh
      have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rwa [e] at this
  have hcard : Nat.card S * Nat.card (R₂ ⊓ Q : Subgroup M) ≤ Nat.card R₂ * Nat.card Q := by
    rw [D.card_S, D.card_Q]
    calc q ^ (3 * n) * Nat.card (R₂ ⊓ Q : Subgroup M) ≤ q ^ (3 * n) * q ^ (n + 1) :=
          Nat.mul_le_mul_left _ hE
      _ = q ^ (2 * n) * q ^ (2 * n + 1) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ Nat.card R₂ * q ^ (2 * n + 1) := Nat.mul_le_mul_right _ hR₂card
  have hsup : R₂ ⊔ Q = S :=
    sup_eq_of_card_ge hR₂S D.Q_le_S (hR₂S.trans hSnorm) hcard
  let C : Subgroup M :=
    { carrier := {t | t ∈ S ∧ ⁅t, v₂⁆ ∈ Z}
      mul_mem' := by
        rintro t t' ⟨ht, htv⟩ ⟨ht', ht'v⟩
        refine ⟨S.mul_mem ht ht', ?_⟩
        have e : ⁅t * t', v₂⁆ = (t * ⁅t', v₂⁆ * t⁻¹) * ⁅t, v₂⁆ := by
          simp only [commutatorElement_def]
          group
        have e2 : t * ⁅t', v₂⁆ * t⁻¹ = ⁅t', v₂⁆ := by
          have := D.Z_central _ ht'v t ht
          calc t * ⁅t', v₂⁆ * t⁻¹ = ⁅t', v₂⁆ * t * t⁻¹ := by rw [this]
            _ = ⁅t', v₂⁆ := by group
        rw [e, e2]
        exact Z.mul_mem ht'v htv
      one_mem' := ⟨S.one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro t ⟨ht, htv⟩
        refine ⟨S.inv_mem ht, ?_⟩
        have e : ⁅t⁻¹, v₂⁆ = t⁻¹ * ⁅t, v₂⁆⁻¹ * t := by
          simp only [commutatorElement_def]
          group
        have e2 : t⁻¹ * ⁅t, v₂⁆⁻¹ * t = ⁅t, v₂⁆⁻¹ := by
          have := D.Z_central _ (Z.inv_mem htv) t ht
          calc t⁻¹ * ⁅t, v₂⁆⁻¹ * t = t⁻¹ * (⁅t, v₂⁆⁻¹ * t) := by group
            _ = t⁻¹ * (t * ⁅t, v₂⁆⁻¹) := by rw [← this]
            _ = ⁅t, v₂⁆⁻¹ := by group
        rw [e, e2]
        exact Z.inv_mem htv }
  have hR₂C : R₂ ≤ C := by
    intro t ht
    refine ⟨hR₂S ht, ?_⟩
    have h := hR₂v t ht
    have : ⁅t, v₂⁆ = 1 := by
      simp only [commutatorElement_def]
      calc t * v₂ * t⁻¹ * v₂⁻¹ = (v₂ * t) * t⁻¹ * v₂⁻¹ := by rw [h]
        _ = 1 := by group
    rw [this]
    exact Z.one_mem
  have hQC : Q ≤ C := fun t ht => ⟨D.Q_le_S ht, D.Q_comm t ht v₂ hv₂Q⟩
  have hSC' : S ≤ C := by
    rw [← hsup]
    exact sup_le hR₂C hQC
  obtain ⟨s', hs', hs'Z⟩ := D.v_not_cent y₂ hy₂M
  exact hs'Z (hSC' hs').2

end CFSG.Quasithin.H13.F431.NF
