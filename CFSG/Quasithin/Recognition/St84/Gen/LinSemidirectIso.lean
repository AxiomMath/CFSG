module

public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
import CFSG.GroupTheory.InternalSemidirectEquiv

public section

namespace CFSG.Quasithin.F112R.St84

open Subgroup

private lemma actsByMatrix_unique {G : Type*} [Group G] {F : Type*} [Field F] {n : ℕ}
    {Q : Subgroup G} {β : ↥Q ≃* Multiplicative (Fin n → F)} {p : G}
    (hnorm : ∀ x : ↥Q, ∃ y : ↥Q, (y : G) = p * x * p⁻¹)
    {A B : Matrix (Fin n) (Fin n) F}
    (hA : ActsByMatrix β p A) (hB : ActsByMatrix β p B) : A = B := by
  apply Matrix.ext_of_mulVec_single
  intro j
  obtain ⟨x, hx⟩ := β.surjective (Multiplicative.ofAdd (Pi.single j 1))
  obtain ⟨y, hy⟩ := hnorm x
  have h1 := hA x y hy
  have h2 := hB x y hy
  rw [hx] at h1 h2
  simpa using h1.symm.trans h2

private lemma actsByMatrix_mul {G : Type*} [Group G] {F : Type*} [Field F] {n : ℕ}
    {Q : Subgroup G} {β : ↥Q ≃* Multiplicative (Fin n → F)} {p q : G}
    (hnormq : ∀ x : ↥Q, ∃ y : ↥Q, (y : G) = q * x * q⁻¹)
    {A B : Matrix (Fin n) (Fin n) F}
    (hA : ActsByMatrix β p A) (hB : ActsByMatrix β q B) :
    ActsByMatrix β (p * q) (A * B) := by
  intro x y hy
  obtain ⟨z, hz⟩ := hnormq x
  have hy' : (y : G) = p * z * p⁻¹ := by
    rw [hy, hz]
    group
  have h1 := hA z y hy'
  have h2 := hB x z hz
  rw [h1, h2, Matrix.mulVec_mulVec]

private lemma actsByMatrix_one_of_comm {G : Type*} [Group G] {F : Type*} [Field F] {n : ℕ}
    {Q : Subgroup G} {β : ↥Q ≃* Multiplicative (Fin n → F)}
    (hcomm : ∀ a b : ↥Q, a * b = b * a) (q : ↥Q) :
    ActsByMatrix β (q : G) (1 : Matrix (Fin n) (Fin n) F) := by
  intro x y hy
  have hyq : y = x := by
    apply Subtype.ext
    rw [hy]
    have hqx : (q : G) * (x : G) = (x : G) * (q : G) := congrArg Subtype.val (hcomm q x)
    rw [hqx]
    group
  rw [hyq]
  simp

private lemma exists_matrixMulEquiv {G : Type*} [Group G] {F : Type*} [Field F] {n : ℕ}
    {P Q X : Subgroup G} {Γ : Subgroup (GL (Fin n) F)}
    (hle : Q ≤ P) (hXle : X ≤ P) (hXQ : X ⊓ Q = ⊥) (hXsup : Q ⊔ X = P)
    (hnormal : P ≤ Subgroup.normalizer (Q : Set G))
    (hcent : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (β : ↥Q ≃* Multiplicative (Fin n → F))
    (hact : ∀ p ∈ P, ∃ A ∈ Γ, ActsByMatrix β p (A : Matrix (Fin n) (Fin n) F))
    (hsurj : ∀ A ∈ Γ, ∃ p ∈ P, ActsByMatrix β p (A : Matrix (Fin n) (Fin n) F)) :
    ∃ Λ : ↥(X.subgroupOf P) ≃* ↥Γ,
      ∀ k : ↥(X.subgroupOf P),
        ActsByMatrix β ((k : ↥P) : G)
          (((Λ k : ↥Γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  classical
  have hnormP : ∀ p : ↥P, ∀ x : ↥Q, ∃ y : ↥Q, (y : G) = (p : G) * x * (p : G)⁻¹ := by
    intro p x
    exact ⟨⟨(p : G) * x * (p : G)⁻¹,
      (Subgroup.le_normalizer_iff.mp hnormal) p p.2 x x.2⟩, rfl⟩
  let Agl : ↥P → GL (Fin n) F := fun p => Classical.choose (hact p p.2)
  have hAgl_mem : ∀ p, Agl p ∈ Γ := fun p => (Classical.choose_spec (hact p p.2)).1
  have hAgl_act : ∀ p : ↥P, ActsByMatrix β (p : G)
      (((Agl p : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) := fun p =>
    (Classical.choose_spec (hact p p.2)).2
  let A : ↥P → Matrix (Fin n) (Fin n) F := fun p =>
    ((Agl p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hA_act : ∀ p : ↥P, ActsByMatrix β (p : G) (A p) := fun p => hAgl_act p
  have huniq : ∀ (p : ↥P) {B : Matrix (Fin n) (Fin n) F},
      ActsByMatrix β (p : G) B → A p = B :=
    fun p B hB => actsByMatrix_unique (hnormP p) (hA_act p) hB
  have hA_mul : ∀ p q : ↥P, A (p * q) = A p * A q := by
    intro p q
    refine huniq (p * q) ?_
    have hmul : ActsByMatrix β ((p : G) * (q : G)) (A p * A q) :=
      actsByMatrix_mul (hnormP q) (hA_act p) (hA_act q)
    simpa using hmul
  have hA_one : A 1 = 1 := by
    refine huniq 1 ?_
    intro x y hy
    have hyx : y = x := by
      apply Subtype.ext
      simpa using hy
    rw [hyx]
    simp
  have hcommQ : ∀ a b : ↥Q, a * b = b * a := by
    intro a b
    apply β.injective
    rw [map_mul, map_mul, mul_comm]
  have hA_Q_one : ∀ q : ↥Q, A ⟨(q : G), hle q.2⟩ = 1 := by
    intro q
    refine huniq ⟨(q : G), hle q.2⟩ ?_
    simpa using actsByMatrix_one_of_comm hcommQ q
  have hsupP : Q.subgroupOf P ⊔ X.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hle hXle, hXsup, Subgroup.subgroupOf_self]
  haveI : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnormal
  let matK : ↥(X.subgroupOf P) →* ↥Γ :=
    { toFun := fun k => ⟨Agl (k : ↥P), hAgl_mem _⟩
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        simpa [A] using hA_one
      map_mul' := fun k l => by
        apply Subtype.ext
        apply Units.ext
        simpa [A] using hA_mul (k : ↥P) (l : ↥P) }
  have matK_inj : Function.Injective matK := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkA : A (k : ↥P) = 1 := by
      have h := congrArg (fun z : ↥Γ =>
        ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hk
      have hk1 : ((matK k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
        simpa using h
      simpa [matK, A] using hk1
    have hcentral : ((k : ↥P) : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨y, hy⟩ := hnormP (k : ↥P) ⟨q, hq⟩
      have h1 := hA_act (k : ↥P) ⟨q, hq⟩ y hy
      rw [hkA] at h1
      simp only [Matrix.one_mulVec] at h1
      have hyq : y = ⟨q, hq⟩ := β.injective h1
      have hxy : ((k : ↥P) : G) * q * ((k : ↥P) : G)⁻¹ = q := by
        rw [← hy, hyq]
      calc
        q * ((k : ↥P) : G) =
            (((k : ↥P) : G) * q * ((k : ↥P) : G)⁻¹) * ((k : ↥P) : G) := by
          rw [hxy]
        _ = ((k : ↥P) : G) * q := by group
    have hkQ : ((k : ↥P) : G) ∈ Q := hcent ⟨(k : ↥P).2, hcentral⟩
    have hkX : ((k : ↥P) : G) ∈ X := k.2
    have hkbot : ((k : ↥P) : G) ∈ (⊥ : Subgroup G) := by
      have hmem : ((k : ↥P) : G) ∈ X ⊓ Q := ⟨hkX, hkQ⟩
      rwa [hXQ] at hmem
    have hk1 : ((k : ↥P) : G) = 1 := by simpa using hkbot
    exact Subtype.ext (Subtype.ext hk1)
  have matK_surj : Function.Surjective matK := by
    intro AΓ
    obtain ⟨p, hp, hActs⟩ := hsurj (AΓ : GL (Fin n) F) AΓ.2
    let pP : ↥P := ⟨p, hp⟩
    have hAp : A pP = ((AΓ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := huniq pP hActs
    have hx : pP ∈ (↑(Q.subgroupOf P ⊔ X.subgroupOf P) : Set ↥P) := by
      rw [hsupP]
      exact Subgroup.mem_top pP
    rw [Subgroup.normal_mul (Q.subgroupOf P) (X.subgroupOf P)] at hx
    obtain ⟨q, hq, k, hk, hqk⟩ := hx
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change A k = ((AΓ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [← hAp]
    rw [← hqk, hA_mul]
    have hqA : A q = 1 := by
      simpa using hA_Q_one ⟨((q : ↥P) : G), hq⟩
    rw [hqA, one_mul]
  refine ⟨MulEquiv.ofBijective matK ⟨matK_inj, matK_surj⟩, ?_⟩
  intro k
  change ActsByMatrix β ((k : ↥P) : G)
    (((matK k : ↥Γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  simpa [matK, A] using hA_act (k : ↥P)

theorem IsLinSemidirect.exists_mulEquiv {G Y : Type*} [Group G] [Group Y]
    {P Q : Subgroup G} {M V : Subgroup Y} {F : Type*} [Field F] {n : ℕ}
    {Γ : Subgroup (GL (Fin n) F)}
    (h : IsLinSemidirect P Q Γ) (h' : IsLinSemidirect M V Γ) :
    ∃ ψ : ↥P ≃* ↥M, ∀ x : ↥P, (x : G) ∈ Q ↔ ((ψ x : ↥M) : Y) ∈ V := by
  classical
  obtain ⟨β, hactP, hsurjP⟩ := h.act
  obtain ⟨β', hactM, hsurjM⟩ := h'.act
  obtain ⟨X, hXle, hXQ, hXsup⟩ := h.split
  obtain ⟨X', hX'le, hX'V, hX'sup⟩ := h'.split
  obtain ⟨Λ1, hΛ1⟩ :=
    exists_matrixMulEquiv (G := G) h.le hXle hXQ hXsup h.normal h.cent β hactP hsurjP
  obtain ⟨Λ2, hΛ2⟩ :=
    exists_matrixMulEquiv (G := Y) h'.le hX'le hX'V hX'sup h'.normal h'.cent β' hactM hsurjM
  let Q1 : Subgroup ↥P := Q.subgroupOf P
  let K1 : Subgroup ↥P := X.subgroupOf P
  let Q2 : Subgroup ↥M := V.subgroupOf M
  let K2 : Subgroup ↥M := X'.subgroupOf M
  haveI hQ1 : Q1.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  haveI hQ2 : Q2.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h'.le).mpr h'.normal
  have hsup1 : Q1 ⊔ K1 = ⊤ := by
    dsimp [Q1, K1]
    rw [← Subgroup.subgroupOf_sup h.le hXle, hXsup, Subgroup.subgroupOf_self]
  have hinf1 : Q1 ⊓ K1 = ⊥ := by
    dsimp [Q1, K1]
    have h : Q.subgroupOf P ⊓ X.subgroupOf P = (Q ⊓ X).subgroupOf P := by
      ext x
      simp [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [h, inf_comm, hXQ, Subgroup.bot_subgroupOf]
  have hdisj1 : Disjoint Q1 K1 := by rw [disjoint_iff, hinf1]
  have hK1norm : K1 ≤ Subgroup.normalizer (Q1 : Set ↥P) := Subgroup.le_normalizer_of_normal
  have hsup2 : Q2 ⊔ K2 = ⊤ := by
    dsimp [Q2, K2]
    rw [← Subgroup.subgroupOf_sup h'.le hX'le, hX'sup, Subgroup.subgroupOf_self]
  have hinf2 : Q2 ⊓ K2 = ⊥ := by
    dsimp [Q2, K2]
    have h : V.subgroupOf M ⊓ X'.subgroupOf M = (V ⊓ X').subgroupOf M := by
      ext x
      simp [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [h, inf_comm, hX'V, Subgroup.bot_subgroupOf]
  have hdisj2 : Disjoint Q2 K2 := by rw [disjoint_iff, hinf2]
  have hK2norm : K2 ≤ Subgroup.normalizer (Q2 : Set ↥M) := Subgroup.le_normalizer_of_normal
  let θ : ↥Q ≃* ↥V := β.trans β'.symm
  let Θ : ↥Q1 ≃* ↥Q2 :=
    (Subgroup.subgroupOfEquivOfLe h.le).trans
      (θ.trans (Subgroup.subgroupOfEquivOfLe h'.le).symm)
  let Λ : ↥K1 ≃* ↥K2 := Λ1.trans Λ2.symm
  have hΘ_val : ∀ q : ↥Q1,
      (((Θ q : ↥Q2) : ↥M) : Y) = (((θ ⟨((q : ↥P) : G), q.2⟩) : ↥V) : Y) := by
    intro q
    rfl
  have hΘ_beta : ∀ q : ↥Q1,
      β' ⟨(((Θ q : ↥Q2) : ↥M) : Y), (Θ q).2⟩ = β ⟨((q : ↥P) : G), q.2⟩ := by
    intro q
    have h := hΘ_val q
    have h' : (⟨(((Θ q : ↥Q2) : ↥M) : Y), (Θ q).2⟩ : ↥V) =
        θ ⟨((q : ↥P) : G), q.2⟩ := Subtype.ext h
    rw [h']
    change β' (β'.symm (β ⟨((q : ↥P) : G), q.2⟩)) = β ⟨((q : ↥P) : G), q.2⟩
    exact MulEquiv.apply_symm_apply β' _
  have hΛ_act : ∀ k : ↥K1,
      ActsByMatrix β' (((Λ k : ↥K2) : ↥M) : Y)
        (((Λ1 k : ↥Γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    intro k
    simpa [Λ] using hΛ2 (Λ k)
  have hinter : ∀ (k : ↥K1) (q : ↥Q1) (hq : (k : ↥P) * q * (k : ↥P)⁻¹ ∈ Q1),
      ((Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩ : ↥Q2) : ↥M) =
        (Λ k : ↥M) * (Θ q : ↥M) * (Λ k : ↥M)⁻¹ := by
    intro k q hq
    let qQ : ↥Q := ⟨((q : ↥P) : G), q.2⟩
    let q' : ↥Q := ⟨↑((k : ↥P) * q * (k : ↥P)⁻¹ : ↥P), hq⟩
    let z : ↥Q2 := ⟨(Λ k : ↥M) * (Θ q : ↥M) * (Λ k : ↥M)⁻¹,
      (Subgroup.le_normalizer_iff.mp hK2norm) (Λ k) (Λ k).2 (Θ q) (Θ q).2⟩
    have hz : (z : ↥M) = (Λ k : ↥M) * (Θ q : ↥M) * (Λ k : ↥M)⁻¹ := rfl
    have hz_eq : z = Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩ := by
      have hb : β' ⟨((z : ↥M) : Y), z.2⟩ =
          β' ⟨((((Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩ : ↥Q2)) : ↥M) : Y),
            (Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩).2⟩ := by
        have hL : β' ⟨((z : ↥M) : Y), z.2⟩ =
            Matrix.mulVec (((Λ1 k : ↥Γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
              (β ⟨((q : ↥P) : G), q.2⟩) := by
          have h1 := hΛ_act k ⟨(((Θ q : ↥Q2) : ↥M) : Y), (Θ q).2⟩
            ⟨((z : ↥M) : Y), z.2⟩ (by
            dsimp [z])
          rw [hΘ_beta] at h1
          exact h1
        have hR : β' ⟨((((Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩ : ↥Q2)) : ↥M) : Y),
            (Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩).2⟩ =
            Matrix.mulVec (((Λ1 k : ↥Γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
              (β ⟨((q : ↥P) : G), q.2⟩) := by
          rw [hΘ_beta]
          have h2 := hΛ1 k qQ q' (by
            dsimp [q', qQ])
          exact h2
        rw [hL, hR]
      have hv : (⟨((z : ↥M) : Y), z.2⟩ : ↥V) =
          ⟨((((Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩ : ↥Q2)) : ↥M) : Y),
            (Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩).2⟩ := β'.injective hb
      have hY : (((z : ↥M) : Y)) =
          ((((Θ ⟨(k : ↥P) * q * (k : ↥P)⁻¹, hq⟩ : ↥Q2) : ↥M) : Y)) :=
        congrArg (fun v : ↥V => (v : Y)) hv
      exact Subtype.ext (Subtype.ext hY)
    rw [← hz_eq]
  obtain ⟨α, hαq, hαk⟩ :=
    CFSG.GroupTheory.exists_mulEquiv_sup_extend
      (G := ↥P) (G' := ↥M) (Q := Q1) (K := K1) (Q' := Q2) (K' := K2)
      hK1norm hdisj1 hK2norm hdisj2 Θ Λ hinter
  let eP : ↥(Q1 ⊔ K1) ≃* ↥P :=
    (MulEquiv.subgroupCongr hsup1).trans Subgroup.topEquiv
  let eM : ↥(Q2 ⊔ K2) ≃* ↥M :=
    (MulEquiv.subgroupCongr hsup2).trans Subgroup.topEquiv
  have eP_apply : ∀ x : ↥(Q1 ⊔ K1), (eP x : ↥P) = (x : ↥P) := fun x => rfl
  have eM_apply : ∀ x : ↥(Q2 ⊔ K2), (eM x : ↥M) = (x : ↥M) := fun x => rfl
  let ψ : ↥P ≃* ↥M := (eP.symm.trans α).trans eM
  have hψq : ∀ q : ↥Q1, ψ (q : ↥P) = (Θ q : ↥M) := by
    intro q
    have h1 : eP.symm (q : ↥P) = ⟨q, Subgroup.mem_sup_left q.2⟩ := by
      apply eP.injective
      rw [MulEquiv.apply_symm_apply]
      exact (eP_apply ⟨q, Subgroup.mem_sup_left q.2⟩).symm
    have h2 : eM (α ⟨q, Subgroup.mem_sup_left q.2⟩) = (Θ q : ↥M) := by
      apply Subtype.ext
      rw [eM_apply]
      exact congrArg (fun z : ↥M => (z : Y)) (hαq q)
    dsimp [ψ]
    rw [h1]
    exact h2
  have hψk : ∀ k : ↥K1, ψ (k : ↥P) = (Λ k : ↥M) := by
    intro k
    have h1 : eP.symm (k : ↥P) = ⟨k, Subgroup.mem_sup_right k.2⟩ := by
      apply eP.injective
      rw [MulEquiv.apply_symm_apply]
      exact (eP_apply ⟨k, Subgroup.mem_sup_right k.2⟩).symm
    have h2 : eM (α ⟨k, Subgroup.mem_sup_right k.2⟩) = (Λ k : ↥M) := by
      apply Subtype.ext
      rw [eM_apply]
      exact congrArg (fun z : ↥M => (z : Y)) (hαk k)
    dsimp [ψ]
    rw [h1]
    exact h2
  have hdecomp : ∀ x : ↥P, ∃ (q : ↥Q1) (k : ↥K1), (q : ↥P) * (k : ↥P) = x := by
    intro x
    have hx : x ∈ (↑(Q1 ⊔ K1) : Set ↥P) := by
      rw [hsup1]
      exact Subgroup.mem_top x
    rw [Subgroup.normal_mul Q1 K1] at hx
    obtain ⟨q, hq, k, hk, hqk⟩ := hx
    exact ⟨⟨q, hq⟩, ⟨k, hk⟩, hqk⟩
  refine ⟨ψ, ?_⟩
  intro x
  obtain ⟨q, k, hqk⟩ := hdecomp x
  constructor
  · intro hx
    have hxQ1 : x ∈ Q1 := hx
    have hkQ : (k : ↥P) ∈ Q1 := by
      have hk_eq : (k : ↥P) = (q : ↥P)⁻¹ * x := by
        rw [← hqk, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hk_eq]
      exact Subgroup.mul_mem Q1 (Subgroup.inv_mem Q1 q.2) hxQ1
    have hkbot : (k : ↥P) ∈ (⊥ : Subgroup ↥P) := by
      have hmem : (k : ↥P) ∈ Q1 ⊓ K1 := ⟨hkQ, k.2⟩
      rwa [hinf1] at hmem
    have hk1 : k = 1 := Subtype.ext (by simpa using hkbot)
    have hxq : x = (q : ↥P) := by
      rw [← hqk, hk1]
      simp
    rw [hxq, hψq]
    exact (Θ q).2
  · intro hxV
    have hψx : ψ x = (Θ q : ↥M) * (Λ k : ↥M) := by
      rw [← hqk, map_mul, hψq, hψk]
    have hΛk_V : ((Λ k : ↥M) : Y) ∈ V := by
      have hψx' : ((ψ x : ↥M) : Y) =
          ((Θ q : ↥M) : Y) * ((Λ k : ↥M) : Y) := by
        simpa using congrArg (fun z : ↥M => (z : Y)) hψx
      have h1 : ((Λ k : ↥M) : Y) = ((Θ q : ↥M) : Y)⁻¹ * ((ψ x : ↥M) : Y) := by
        rw [hψx']
        group
      rw [h1]
      exact Subgroup.mul_mem V (Subgroup.inv_mem V (Θ q).2) hxV
    have hΛk_X : ((Λ k : ↥M) : Y) ∈ X' := (Λ k).2
    have hΛk_bot : ((Λ k : ↥M) : Y) ∈ (⊥ : Subgroup Y) := by
      have hmem : ((Λ k : ↥M) : Y) ∈ X' ⊓ V := ⟨hΛk_X, hΛk_V⟩
      rw [hX'V] at hmem
      simpa using hmem
    have hΛk1 : (Λ k : ↥M) = 1 := by
      apply Subtype.ext
      simpa using hΛk_bot
    have hΛk1' : Λ k = 1 := Subtype.ext (by simpa using hΛk1)
    have hk1 : k = 1 := Λ.injective (by rw [hΛk1', map_one])
    rw [← hqk, hk1]
    simp only [Subgroup.coe_mul, Subgroup.coe_one, mul_one]
    exact q.2

end CFSG.Quasithin.F112R.St84
