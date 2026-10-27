module

public import CFSG.Milestones.ASVolI.C31.J4NP.Lemma9
public import CFSG.Milestones.ASVolI.C31.J4NP.Glue

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.J4Loc (omegaZ)

theorem burnsideJ4NP_map_conj_of_mem {G : Type*} [Group G] {K : Subgroup G} {c : G} (hc : c ∈ K) :
    K.map (MulAut.conj c).toMonoidHom = K := by
  ext y
  rw [burnsideJ4NP_mem_map_conj]
  constructor
  · intro h
    have e : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem hc h) (K.inv_mem hc)
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hc) h) hc

theorem burnsideJ4NP_map_conj_inf {G : Type*} [Group G] (X Y : Subgroup G) (c : G) :
    (X ⊓ Y).map (MulAut.conj c).toMonoidHom =
      X.map (MulAut.conj c).toMonoidHom ⊓ Y.map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [burnsideJ4NP_mem_map_conj, Subgroup.mem_inf, Subgroup.mem_inf, burnsideJ4NP_mem_map_conj,
    burnsideJ4NP_mem_map_conj]

theorem burnsideJ4NP_map_conj_one {G : Type*} [Group G] (X : Subgroup G) :
    X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  rw [burnsideJ4NP_mem_map_conj]
  simp

theorem burnsideJ4NP_Eg_map_conj
    {h : J} (hh : h ∈ Hj) : (Eg uJ 11).map (MulAut.conj h).toMonoidHom = Eg uJ 11 := by
  have hN : h⁻¹ ∈ Subgroup.normalizer (Eg uJ 11 : Set J) := by
    rw [normalizer_Eg_eq_Hj j4Facts]
    exact Hj.inv_mem hh
  ext y
  rw [burnsideJ4NP_mem_map_conj]
  have := Subgroup.mem_normalizer_iff.mp hN y
  rw [inv_inv] at this
  exact this.symm

theorem burnsideJ4NP_card_inf_Eg_map_conj
    (B : Subgroup J) {h : J} (hh : h ∈ Hj) :
    Nat.card ↥(B.map (MulAut.conj h).toMonoidHom ⊓ Eg uJ 11) = Nat.card ↥(B ⊓ Eg uJ 11) := by
  calc Nat.card ↥(B.map (MulAut.conj h).toMonoidHom ⊓ Eg uJ 11)
      = Nat.card ↥(B.map (MulAut.conj h).toMonoidHom ⊓
          (Eg uJ 11).map (MulAut.conj h).toMonoidHom) := by rw [burnsideJ4NP_Eg_map_conj hh]
    _ = Nat.card ↥((B ⊓ Eg uJ 11).map (MulAut.conj h).toMonoidHom) := by
        rw [burnsideJ4NP_map_conj_inf]
    _ = Nat.card ↥(B ⊓ Eg uJ 11) := burnsideJ4KW_card_map_conj _ _

theorem burnsideJ4NP_IsHCl_map_conj {A B : Subgroup J} {h : J} (hh : h ∈ Hj)
    (hB : burnsideJ4NP_IsHCl A B) :
    burnsideJ4NP_IsHCl (A.map (MulAut.conj h).toMonoidHom) (B.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨P, hPK, hP2, hPmax, rfl⟩ := hB
  have hK : Hj ⊓ Subgroup.centralizer ((A.map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J) =
      (Hj ⊓ Subgroup.centralizer (A : Set J)).map (MulAut.conj h).toMonoidHom := by
    rw [burnsideJ4NP_centralizer_map_conj, burnsideJ4NP_map_conj_inf,
      burnsideJ4NP_map_conj_of_mem hh]
  refine ⟨P.map (MulAut.conj h).toMonoidHom, ?_, hP2.map _, fun Q hQK hQ2 hPQ => ?_,
    burnsideJ4NP_omegaZ_map_conj P h⟩
  · rw [hK]
    exact Subgroup.map_mono hPK
  · have h1 : Q.map (MulAut.conj h⁻¹).toMonoidHom ≤ Hj ⊓ Subgroup.centralizer (A : Set J) := by
      have := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hQK
      rwa [hK, burnsideJ4NP_map_conj_inv_map_conj] at this
    have h2 : P ≤ Q.map (MulAut.conj h⁻¹).toMonoidHom := by
      have := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hPQ
      rwa [burnsideJ4NP_map_conj_inv_map_conj] at this
    have h3 := congrArg (Subgroup.map (MulAut.conj h).toMonoidHom) (hPmax _ h1 (hQ2.map _) h2)
    have e := burnsideJ4NP_map_conj_inv_map_conj Q h⁻¹
    rw [inv_inv] at e
    rw [← h3, e]

theorem burnsideJ4NP_IsHCl_conj {A B B' : Subgroup J} (hB : burnsideJ4NP_IsHCl A B)
    (hB' : burnsideJ4NP_IsHCl A B') :
    ∃ k ∈ Hj ⊓ Subgroup.centralizer (A : Set J), B' = B.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨P, hPK, hP2, hPmax, rfl⟩ := hB
  obtain ⟨P', hP'K, hP'2, hP'max, rfl⟩ := hB'
  set K := Hj ⊓ Subgroup.centralizer (A : Set J) with hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let mk : ∀ X : Subgroup J, X ≤ K → IsPGroup 2 ↥X →
      (∀ Q : Subgroup J, Q ≤ K → IsPGroup 2 ↥Q → X ≤ Q → Q = X) → Sylow 2 ↥K :=
    fun X hXK hX2 hXmax =>
      { toSubgroup := X.subgroupOf K
        isPGroup' := hX2.comap_subtype
        is_maximal' := fun {Q} hQ2 hXQ => by
          have h1 := hXmax (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ2.map _)
            (fun x hx => ⟨⟨x, hXK hx⟩, hXQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
          ext q
          rw [Subgroup.mem_subgroupOf, ← h1]
          constructor
          · intro hq
            exact ⟨q, hq, rfl⟩
          · rintro ⟨q', hq', hqq'⟩
            exact (Subtype.ext hqq' : q' = q) ▸ hq' }
  have key : ∀ (X₁ X₂ : Subgroup J) (S₁ S₂ : Sylow 2 ↥K) (g : ↥K),
      (S₁ : Subgroup ↥K) = X₁.subgroupOf K → (S₂ : Subgroup ↥K) = X₂.subgroupOf K → X₂ ≤ K →
      g • S₁ = S₂ → X₂ ≤ X₁.map (MulAut.conj (g : J)).toMonoidHom := by
    intro X₁ X₂ S₁ S₂ g h₁ h₂ hX₂ hg y hy
    have hy' : (⟨y, hX₂ hy⟩ : ↥K) ∈ (S₂ : Subgroup ↥K) := by
      rw [h₂]
      exact Subgroup.mem_subgroupOf.mpr hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, h₁] at hy'
    obtain ⟨t, ht, hte⟩ := hy'
    have ht' : (t : J) ∈ X₁ := Subgroup.mem_subgroupOf.mp ht
    have hte' : (g : J) * (t : J) * (g : J)⁻¹ = y := by
      have := congrArg Subtype.val hte
      simpa [MulAut.conj_apply] using this
    rw [burnsideJ4NP_mem_map_conj, ← hte']
    simpa [mul_assoc] using ht'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K (mk P hPK hP2 hPmax) (mk P' hP'K hP'2 hP'max)
  have hg' : g⁻¹ • mk P' hP'K hP'2 hP'max = mk P hPK hP2 hPmax := by rw [← hg, inv_smul_smul]
  have h1 := key P P' _ _ g rfl rfl hP'K hg
  have h2 := key P' P _ _ g⁻¹ rfl rfl hPK hg'
  refine ⟨(g : J), g.2, ?_⟩
  have hP' : P' = P.map (MulAut.conj (g : J)).toMonoidHom := by
    apply le_antisymm h1
    have := Subgroup.map_mono (f := (MulAut.conj (g : J)).toMonoidHom) h2
    rwa [burnsideJ4KW_map_conj_map_conj, Subgroup.coe_inv, mul_inv_cancel,
      burnsideJ4NP_map_conj_one] at this
  rw [hP', burnsideJ4NP_omegaZ_map_conj]

theorem burnsideJ4NP_exists_sylow_eq {G : Type*} [Group G] {K P : Subgroup G} (hPK : P ≤ K)
    (hP2 : IsPGroup 2 ↥P)
    (hPmax : ∀ Q : Subgroup G, Q ≤ K → IsPGroup 2 ↥Q → P ≤ Q → Q = P) :
    ∃ S : Sylow 2 ↥K, (S : Subgroup ↥K) = P.subgroupOf K := by
  refine ⟨{ toSubgroup := P.subgroupOf K
            isPGroup' := hP2.comap_subtype
            is_maximal' := fun {Q} hQ2 hPQ => ?_ }, rfl⟩
  have h1 := hPmax (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ2.map _)
    (fun x hx => ⟨⟨x, hPK hx⟩, hPQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
  ext q
  rw [Subgroup.mem_subgroupOf, ← h1]
  constructor
  · intro hq
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q', hq', hqq'⟩
    exact (Subtype.ext hqq' : q' = q) ▸ hq'

theorem burnsideJ4NP_cover_of_sylow
    {A P : Subgroup J} (ys : List J)
    (hPK : P ≤ Hj ⊓ Subgroup.centralizer (A : Set J)) (hP2 : IsPGroup 2 ↥P)
    (hPmax : ∀ Q : Subgroup J, Q ≤ Hj ⊓ Subgroup.centralizer (A : Set J) → IsPGroup 2 ↥Q →
      P ≤ Q → Q = P)
    (hP : ∀ x ∈ P, burnsideJ4NP_Is2A x → x ∉ A →
      ∃ y ∈ ys, ∃ n ∈ Hj,
        A ⊔ Subgroup.zpowers x = (A ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom) :
    ∀ x ∈ Hj ⊓ Subgroup.centralizer (A : Set J), burnsideJ4NP_Is2A x → x ∉ A →
      ∃ y ∈ ys, ∃ n ∈ Hj,
        A ⊔ Subgroup.zpowers x = (A ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom := by
  intro x hx h2A hxA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : x * x = 1 := by
    obtain ⟨g, rfl⟩ := h2A
    calc g * CFSG.Quasithin.J4Loc.z0 * g⁻¹ * (g * CFSG.Quasithin.J4Loc.z0 * g⁻¹)
        = g * (CFSG.Quasithin.J4Loc.z0 * CFSG.Quasithin.J4Loc.z0) * g⁻¹ := by group
      _ = 1 := by rw [burnsideJ4NP_z0_sq]; group
  have hX2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    have hc : Nat.card (Subgroup.zpowers x) = orderOf x := Nat.card_zpowers x
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hc, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [hc, h]; rfl)
  obtain ⟨S', hS'⟩ :=
    (hX2.comap_subtype (K := Hj ⊓ Subgroup.centralizer (A : Set J))).exists_le_sylow
  obtain ⟨S, hS⟩ := burnsideJ4NP_exists_sylow_eq hPK hP2 hPmax
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Hj ⊓ Subgroup.centralizer (A : Set J)) S S'
  have hxS' : (⟨x, hx⟩ : ↥(Hj ⊓ Subgroup.centralizer (A : Set J))) ∈
      (S' : Subgroup ↥(Hj ⊓ Subgroup.centralizer (A : Set J))) :=
    hS' (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hS] at hxS'
  obtain ⟨t, ht, hte⟩ := hxS'
  have htP : (t : J) ∈ P := Subgroup.mem_subgroupOf.mp ht
  have hte' : (g : J) * (t : J) * (g : J)⁻¹ = x := by
    have := congrArg Subtype.val hte
    simpa [MulAut.conj_apply] using this
  obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp g.2
  have hcomm := Subgroup.mem_centralizer_iff.mp hgC
  have key1 : ∀ b ∈ A, (g : J)⁻¹ * b * (g : J) = b := fun b hb => by
    have h1 := hcomm b hb
    calc (g : J)⁻¹ * b * (g : J) = (g : J)⁻¹ * (b * (g : J)) := by group
      _ = (g : J)⁻¹ * ((g : J) * b) := by rw [h1]
      _ = b := by group
  have key2 : ∀ b ∈ A, (g : J) * b * (g : J)⁻¹ = b := fun b hb => by
    have h1 := hcomm b hb
    calc (g : J) * b * (g : J)⁻¹ = (b * (g : J)) * (g : J)⁻¹ := by rw [h1]
      _ = b := by group
  have hAg : A.map (MulAut.conj (g : J)).toMonoidHom = A := by
    ext a
    rw [burnsideJ4NP_mem_map_conj]
    constructor
    · intro ha
      have h3 : (g : J) * ((g : J)⁻¹ * a * (g : J)) * (g : J)⁻¹ = a := by group
      rw [key2 _ ha] at h3
      rwa [h3] at ha
    · intro ha
      rw [key1 a ha]
      exact ha
  have h2A' : burnsideJ4NP_Is2A (t : J) := by
    have := (burnsideJ4NP_Is2A_conj (g : J)).mp (hte' ▸ h2A)
    exact this
  have htA : (t : J) ∉ A := by
    intro htA
    apply hxA
    rw [← hte', key2 _ htA]
    exact htA
  obtain ⟨y, hy, n, hn, hxy⟩ := hP (t : J) htP h2A' htA
  refine ⟨y, hy, (g : J) * n, Hj.mul_mem hgH hn, ?_⟩
  have e : (MulAut.conj (g : J)).toMonoidHom (t : J) = x := by
    simpa [MulAut.conj_apply] using hte'
  calc A ⊔ Subgroup.zpowers x
      = (A ⊔ Subgroup.zpowers (t : J)).map (MulAut.conj (g : J)).toMonoidHom := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, e, hAg]
    _ = ((A ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom).map
          (MulAut.conj (g : J)).toMonoidHom := by rw [hxy]
    _ = (A ⊔ Subgroup.zpowers y).map (MulAut.conj ((g : J) * n)).toMonoidHom :=
        burnsideJ4KW_map_conj_map_conj _ _ _

theorem burnsideJ4NP_classify_of_data
    (Rep : ℕ → Subgroup J) (N : ℕ)
    (h0 : ∃ k < N, ∃ h ∈ Hj,
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 = (Rep k).map (MulAut.conj h).toMonoidHom)
    (hstep : ∀ k < N, ∀ x ∈ Hj ⊓ Subgroup.centralizer (Rep k : Set J), burnsideJ4NP_Is2A x →
      x ∉ Rep k → ∀ B : Subgroup J, burnsideJ4NP_IsHCl (Rep k ⊔ Subgroup.zpowers x) B →
        Nat.card ↥B ≤ 2 ^ 10 → Nat.card ↥(B ⊓ Eg uJ 11) ≤ 2 ^ 6 →
        ∃ k' < N, ∃ h ∈ Hj, B = (Rep k').map (MulAut.conj h).toMonoidHom) :
    ∀ A : Subgroup J, burnsideJ4NP_ReachP A →
      ∃ k < N, ∃ h ∈ Hj, A = (Rep k).map (MulAut.conj h).toMonoidHom := by
  intro A hA
  induction hA with
  | base => exact h0
  | @step A B x _ hx h2A hxA hcl hB hBE ih =>
    obtain ⟨k, hk, h, hh, rfl⟩ := ih
    have hhi : h⁻¹ ∈ Hj := Hj.inv_mem hh
    have hx' : h⁻¹ * x * h ∈ Hj ⊓ Subgroup.centralizer (Rep k : Set J) := by
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨Hj.mul_mem (Hj.mul_mem hhi hxH) hh, ?_⟩
      have := (Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom)
        (le_of_eq (burnsideJ4NP_centralizer_map_conj (Rep k) h))) ⟨x, hxC, rfl⟩
      rw [burnsideJ4NP_map_conj_inv_map_conj] at this
      simpa [MulAut.conj_apply] using this
    have h2A' : burnsideJ4NP_Is2A (h⁻¹ * x * h) := by
      have := (burnsideJ4NP_Is2A_conj h⁻¹).mpr h2A
      simpa using this
    have hxA' : h⁻¹ * x * h ∉ Rep k := fun hm => hxA (burnsideJ4NP_mem_map_conj.mpr hm)
    have hsup : (Rep k).map (MulAut.conj h).toMonoidHom ⊔ Subgroup.zpowers x =
        (Rep k ⊔ Subgroup.zpowers (h⁻¹ * x * h)).map (MulAut.conj h).toMonoidHom := by
      have e : (MulAut.conj h).toMonoidHom (h⁻¹ * x * h) = x := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, e]
    have hcl' : burnsideJ4NP_IsHCl (Rep k ⊔ Subgroup.zpowers (h⁻¹ * x * h))
        (B.map (MulAut.conj h⁻¹).toMonoidHom) := by
      have := burnsideJ4NP_IsHCl_map_conj hhi hcl
      rwa [hsup, burnsideJ4NP_map_conj_inv_map_conj] at this
    have hB' : Nat.card ↥(B.map (MulAut.conj h⁻¹).toMonoidHom) ≤ 2 ^ 10 := by
      rw [burnsideJ4KW_card_map_conj]
      exact hB
    have hBE' : Nat.card ↥(B.map (MulAut.conj h⁻¹).toMonoidHom ⊓ Eg uJ 11) ≤ 2 ^ 6 := by
      rw [burnsideJ4NP_card_inf_Eg_map_conj B hhi]
      exact hBE
    obtain ⟨k', hk', h', hh', hBeq⟩ := hstep k hk _ hx' h2A' hxA' _ hcl' hB' hBE'
    refine ⟨k', hk', h * h', Hj.mul_mem hh hh', ?_⟩
    have e := burnsideJ4NP_map_conj_inv_map_conj B h⁻¹
    rw [inv_inv, hBeq, burnsideJ4KW_map_conj_map_conj] at e
    exact e.symm

theorem burnsideJ4NP_step_of_children
    (Rep : ℕ → Subgroup J) (N : ℕ) {A : Subgroup J} (ys : List J)
    (hcover : ∀ x ∈ Hj ⊓ Subgroup.centralizer (A : Set J), burnsideJ4NP_Is2A x → x ∉ A →
      ∃ y ∈ ys, ∃ n ∈ Hj,
        A ⊔ Subgroup.zpowers x = (A ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom)
    (hchild : ∀ y ∈ ys, ∃ B₀ : Subgroup J, burnsideJ4NP_IsHCl (A ⊔ Subgroup.zpowers y) B₀ ∧
      (2 ^ 10 < Nat.card ↥B₀ ∨ 2 ^ 6 < Nat.card ↥(B₀ ⊓ Eg uJ 11) ∨
        ∃ k' < N, ∃ h ∈ Hj, B₀ = (Rep k').map (MulAut.conj h).toMonoidHom)) :
    ∀ x ∈ Hj ⊓ Subgroup.centralizer (A : Set J), burnsideJ4NP_Is2A x → x ∉ A →
      ∀ B : Subgroup J, burnsideJ4NP_IsHCl (A ⊔ Subgroup.zpowers x) B → Nat.card ↥B ≤ 2 ^ 10 →
        Nat.card ↥(B ⊓ Eg uJ 11) ≤ 2 ^ 6 →
        ∃ k' < N, ∃ h ∈ Hj, B = (Rep k').map (MulAut.conj h).toMonoidHom := by
  intro x hx h2A hxA B hB hB10 hBE
  obtain ⟨y, hy, n, hn, hxy⟩ := hcover x hx h2A hxA
  obtain ⟨B₀, hB₀, hv⟩ := hchild y hy
  have hB₀n := burnsideJ4NP_IsHCl_map_conj hn hB₀
  rw [← hxy] at hB₀n
  obtain ⟨m, hm, hBm⟩ := burnsideJ4NP_IsHCl_conj hB₀n hB
  have hmH : m ∈ Hj := (Subgroup.mem_inf.mp hm).1
  rw [burnsideJ4KW_map_conj_map_conj] at hBm
  have hmn : m * n ∈ Hj := Hj.mul_mem hmH hn
  rcases hv with h1 | h1 | ⟨k', hk', h, hh, hB₀eq⟩
  · rw [hBm, burnsideJ4KW_card_map_conj] at hB10
    omega
  · rw [hBm, burnsideJ4NP_card_inf_Eg_map_conj B₀ hmn] at hBE
    omega
  · refine ⟨k', hk', m * n * h, Hj.mul_mem hmn hh, ?_⟩
    rw [hBm, hB₀eq, burnsideJ4KW_map_conj_map_conj]

theorem burnsideJ4NP_openReachP_of_data
    (Rep : ℕ → Subgroup J) (N : ℕ)
    (h0 : ∃ k < N, ∃ h ∈ Hj,
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 = (Rep k).map (MulAut.conj h).toMonoidHom)
    (hstep : ∀ k < N, ∀ x ∈ Hj ⊓ Subgroup.centralizer (Rep k : Set J), burnsideJ4NP_Is2A x →
      x ∉ Rep k → ∀ B : Subgroup J, burnsideJ4NP_IsHCl (Rep k ⊔ Subgroup.zpowers x) B →
        Nat.card ↥B ≤ 2 ^ 10 → Nat.card ↥(B ⊓ Eg uJ 11) ≤ 2 ^ 6 →
        ∃ k' < N, ∃ h ∈ Hj, B = (Rep k').map (MulAut.conj h).toMonoidHom)
    (hverdict : ∀ k < N, ∀ R : Subgroup J, burnsideJ4NP_Hyp R → ∀ h ∈ Hj,
      (Rep k).map (MulAut.conj h).toMonoidHom ≤ omegaZ R →
      burnsideJ4NP_W R ≤ (Rep k).map (MulAut.conj h).toMonoidHom →
      ∃ c : J, burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom ≤ burnsideJ4NP_W R) :
    burnsideJ4NP_OpenReachP := by
  intro A hA R hR hAZ hWA
  obtain ⟨k, hk, h, hh, rfl⟩ := burnsideJ4NP_classify_of_data Rep N h0 hstep A hA
  exact hverdict k hk R hR h hh hAZ hWA

theorem burnsideJ4NP_verdict_F {A₀ : Subgroup J} {d : J}
    (hF : burnsideJ4NP_F.map (MulAut.conj d).toMonoidHom ≤
      Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x})
    (R : Subgroup J) (c : J) (hAZ : A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R)
    (hWA : burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom) :
    ∃ e : J, burnsideJ4NP_F.map (MulAut.conj e).toMonoidHom ≤ burnsideJ4NP_W R := by
  refine ⟨c * d, ?_⟩
  rw [burnsideJ4NP_W_eq_closure hAZ hWA, burnsideJ4NP_closure2A_map_conj,
    ← burnsideJ4KW_map_conj_map_conj]
  exact Subgroup.map_mono hF

theorem burnsideJ4NP_verdict_np
    {A₀ : Subgroup J} {g : J}
    (hg : P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer
      ((Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x} : Subgroup J) : Set J))
    {R : Subgroup J} (hR : burnsideJ4NP_Hyp R) (c : J)
    (hAZ : A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R)
    (hWA : burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom) : False :=
  (burnsideJ4NP_survivor hR hAZ hWA rfl).2.2.2.2.2.2.2 g hg

end CFSG.ASVolI
