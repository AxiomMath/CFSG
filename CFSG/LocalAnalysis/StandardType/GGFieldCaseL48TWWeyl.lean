module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48TailCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped Pointwise commutatorElement

namespace GGL48TW

variable {G : Type} [Group G]

theorem closure_conj_le_commutator_sup {K U₁ S : Subgroup G} {W : Set G}
    (hU₁K : U₁ ≤ Subgroup.normalizer (K : Set G)) (hSU₁ : S ≤ U₁)
    (hW : ∀ n ∈ W, ∃ g ∈ Subgroup.normalizer (K : Set G),
      ∃ m ∈ Subgroup.normalizer (U₁ : Set G), n = g * m) :
    Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set G)) ≤
      ⁅Subgroup.normalizer (K : Set G), Subgroup.normalizer (K : Set G)⁆ ⊔ U₁ := by
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨n, hn, s, hs, rfl⟩ := hz
  obtain ⟨g, hg, m, hm, rfl⟩ := hW n hn
  have hu : m * s * m⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp hm s).mp (hSU₁ hs)
  have hcomm : ⁅g, m * s * m⁻¹⁆ ∈
      ⁅Subgroup.normalizer (K : Set G), Subgroup.normalizer (K : Set G)⁆ :=
    Subgroup.commutator_mem_commutator hg (hU₁K hu)
  have e : g * m * s * (g * m)⁻¹ = ⁅g, m * s * m⁻¹⁆ * (m * s * m⁻¹) := by
    rw [commutatorElement_def]; group
  rw [SetLike.mem_coe, e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hu)

variable [Finite G]

theorem exists_conj_le_of_maximal {p : ℕ} [Fact p.Prime] {C U P : Subgroup G}
    (hUC : U ≤ C) (hUp : IsPGroup p U)
    (hUmax : ∀ R : Subgroup G, R ≤ C → IsPGroup p R → U ≤ R → R = U)
    (hPC : P ≤ C) (hPp : IsPGroup p P) :
    ∃ g ∈ C, ∀ y ∈ P, g⁻¹ * y * g ∈ U := by
  let SU : Sylow p C := GGL48.sylowSubgroupOf hUp hUC hUmax
  have hP' : IsPGroup p (P.subgroupOf C) := hPp.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C SU S
  refine ⟨g, g.2, fun y hy => ?_⟩
  have hyS : (⟨y, hPC hy⟩ : C) ∈ (S : Subgroup C) := hS (by simpa [Subgroup.mem_subgroupOf])
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyS
  obtain ⟨s, hs, hsy⟩ := hyS
  have hsU : (s : G) ∈ U := by
    have : s ∈ (SU : Subgroup C) := hs
    rw [GGL48.coe_sylowSubgroupOf, Subgroup.mem_subgroupOf] at this
    exact this
  have hval : (g : G) * s * (g : G)⁻¹ = y := by
    have := congrArg Subtype.val hsy
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [← hval]
  simpa [mul_assoc] using hsU

theorem exists_mul_of_mem_normalizer {p : ℕ} [Fact p.Prime] {B₁ U U₁ : Subgroup G}
    (hUC : U ≤ Subgroup.centralizer (B₁ : Set G)) (hUp : IsPGroup p U)
    (hUmax : ∀ R : Subgroup G, R ≤ Subgroup.centralizer (B₁ : Set G) → IsPGroup p R → U ≤ R →
      R = U)
    (hNU : Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (B₁ : Set G) ≤
      Subgroup.normalizer (U₁ : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (B₁ : Set G)) :
    ∃ g ∈ Subgroup.centralizer (B₁ : Set G), ∃ m ∈ Subgroup.normalizer (U₁ : Set G),
      n = g * m := by
  set C := Subgroup.centralizer (B₁ : Set G) with hC
  let U' := U.map (MulAut.conj n).toMonoidHom
  have hninv : ∀ b ∈ B₁, n⁻¹ * b * n ∈ B₁ := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * b * n)).mpr (by simpa [mul_assoc] using hb)
  have hU'C : U' ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro b hb
    have hcomm := Subgroup.mem_centralizer_iff.mp (hUC hu) _ (hninv b hb)
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc b * (n * u * n⁻¹) = n * ((n⁻¹ * b * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * b * n)) * n⁻¹ := by rw [hcomm]
      _ = n * u * n⁻¹ * b := by group
  obtain ⟨g, hgC, hg⟩ := exists_conj_le_of_maximal hUC hUp hUmax hU'C (hUp.map _)
  have hle : U' ≤ U.map (MulAut.conj g).toMonoidHom := by
    intro y hy
    refine ⟨g⁻¹ * y * g, hg y hy, ?_⟩
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have heq : U' = U.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (MulAut.conj n).injective])
  have hgN : g ∈ Subgroup.normalizer (B₁ : Set G) := Subgroup.centralizer_le_normalizer _ hgC
  refine ⟨g, hgC, g⁻¹ * n, hNU ⟨?_, (Subgroup.normalizer (B₁ : Set G)).mul_mem
    ((Subgroup.normalizer (B₁ : Set G)).inv_mem hgN) hn⟩, by group⟩
  show g⁻¹ * n ∈ Subgroup.normalizer (U : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : n * y * n⁻¹ ∈ U' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rw [heq] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : g⁻¹ * n * y * (g⁻¹ * n)⁻¹ = z := by
      calc g⁻¹ * n * y * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * y * n⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hzy]
        _ = z := by group
    rw [this]; exact hz
  · intro hy
    have h1 : g * (g⁻¹ * n * y * (g⁻¹ * n)⁻¹) * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom :=
      ⟨_, hy, by simp [MulAut.conj_apply]⟩
    rw [← heq] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : y = z := by
      have e : g * (g⁻¹ * n * y * (g⁻¹ * n)⁻¹) * g⁻¹ = n * y * n⁻¹ := by group
      rw [e] at hzy
      have := congrArg (fun w => n⁻¹ * w * n) hzy
      simpa [mul_assoc] using this.symm
    rw [this]; exact hz

theorem mem_commutator_sup_of_weyl {p : ℕ} [Fact p.Prime] {B₁ U U₁ K S : Subgroup G}
    {W : Set G} {x : G}
    (hUC : U ≤ Subgroup.centralizer (B₁ : Set G)) (hUp : IsPGroup p U)
    (hUmax : ∀ R : Subgroup G, R ≤ Subgroup.centralizer (B₁ : Set G) → IsPGroup p R → U ≤ R →
      R = U)
    (hNU : Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (B₁ : Set G) ≤
      Subgroup.normalizer (U₁ : Set G))
    (hCK : Subgroup.centralizer (B₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hU₁K : U₁ ≤ Subgroup.normalizer (K : Set G)) (hUK : U ⊓ K ≤ U₁)
    (hSp : IsPGroup p S) (hSC : S ≤ Subgroup.centralizer (B₁ : Set G)) (hSK : S ≤ K)
    (hWN : W ⊆ Subgroup.normalizer (B₁ : Set G))
    (hx : x ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set G))) :
    x ∈ ⁅Subgroup.normalizer (K : Set G), Subgroup.normalizer (K : Set G)⁆ ⊔ U₁ := by
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_maximal hUC hUp hUmax hSC hSp
  set S' := S.map (MulAut.conj c⁻¹).toMonoidHom with hS'
  set W' := (fun n => n * c) '' W with hW'
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := hCK hcC
  have hS'U₁ : S' ≤ U₁ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine hUK ⟨hc s hs, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hcK) s).mp
      (hSK hs)
    simpa using this
  have hcN : c ∈ Subgroup.normalizer (B₁ : Set G) := Subgroup.centralizer_le_normalizer _ hcC
  have hW'fac : ∀ n ∈ W', ∃ g ∈ Subgroup.normalizer (K : Set G),
      ∃ m ∈ Subgroup.normalizer (U₁ : Set G), n = g * m := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨g, hgC, m, hm, he⟩ := exists_mul_of_mem_normalizer hUC hUp hUmax hNU
      ((Subgroup.normalizer (B₁ : Set G)).mul_mem (hWN hn) hcN)
    exact ⟨g, hCK hgC, m, hm, he⟩
  refine closure_conj_le_commutator_sup hU₁K hS'U₁ hW'fac ?_
  refine (Subgroup.closure_mono ?_) hx
  intro z hz
  simp only [Set.mem_iUnion, Set.mem_image] at hz ⊢
  obtain ⟨n, hn, s, hs, rfl⟩ := hz
  refine ⟨n * c, ⟨n, hn, rfl⟩, c⁻¹ * s * c, ⟨s, hs, ?_⟩, by group⟩
  simp [MulAut.conj_apply]

theorem not_mem_sup_of_pElement_mem {p : ℕ} [hp : Fact p.Prime] {N Q B : Subgroup G} {x : G}
    (hQN : Q ≤ N) (hnorm : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) (hBN : B ≤ N) (hxN : x ∈ N)
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) (hxQ : x ∉ Q)
    (hB : ∀ c ∈ B, (∃ k : ℕ, c ^ p ^ k = 1) → c ∈ Q) : x ∉ Q ⊔ B := by
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hnorm b (hBN hb) g
    · intro hg
      have := hnorm b⁻¹ (N.inv_mem (hBN hb)) _ hg
      have e : b⁻¹ * (b * g * b⁻¹) * b⁻¹⁻¹ = g := by group
      rwa [e] at this
  intro hx
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right B Q hBQ] at hx
  obtain ⟨b, hb, q, hq, hbq⟩ := hx
  have hqinv : q⁻¹ ∈ Q := Q.inv_mem hq
  have hpow : ∀ m : ℕ, (x * q⁻¹) ^ m * (x ^ m)⁻¹ ∈ Q := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x * q⁻¹) ^ (m + 1) * (x ^ (m + 1))⁻¹ =
          ((x * q⁻¹) ^ m * (x ^ m)⁻¹) * (x ^ (m + 1) * q⁻¹ * (x ^ (m + 1))⁻¹) := by
        rw [pow_succ, pow_succ]; group
      rw [e]
      exact Q.mul_mem ih (hnorm _ (N.pow_mem hxN _) _ hqinv)
  have hbx : b = x * q⁻¹ := by rw [← hbq]; group
  set o := orderOf b with ho
  have ho0 : o ≠ 0 := (orderOf_pos b).ne'
  set r := ordCompl[p] o with hr
  have hbr : b ^ r ∈ Q := by
    refine hB _ (B.pow_mem hb r) ⟨o.factorization p, ?_⟩
    rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, ho, pow_orderOf_eq_one]
  have hxr : x ^ r ∈ Q := by
    have h1 := hpow r
    rw [← hbx] at h1
    have e : x ^ r = (b ^ r * (x ^ r)⁻¹)⁻¹ * b ^ r := by group
    rw [e]
    exact Q.mul_mem (Q.inv_mem h1) hbr
  obtain ⟨k, hk⟩ := hxp
  have hcop : r.Coprime (orderOf x) := by
    have h1 : (p ^ k).Coprime r := Nat.Coprime.pow_left k (Nat.coprime_ordCompl hp.out ho0)
    exact (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk) h1).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact hxQ (hm ▸ Q.pow_mem hxr m)

end GGL48TW

theorem not_mem_lField_of_torusWeyl {G : Type} [Group G] [Finite G]
    (hF : GGL48NbrFieldInput) (hT : GGL48TorusWeylCentInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (hJK : J ≤ K) (hUK : U ⊓ K ≤ U₁) :
    x ∉ ⁅Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
          Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)⁆ ⊔
        ggL48U2 x U₁ ⊔ (L ⊓ Subgroup.centralizer
          ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hcan, hX1, hX2, hX3, hX4, hX5⟩, -, h43, -, -, h44, h45, hID, hNU⟩ := id hS
  obtain ⟨hDd, hd1, hNbr, hyd, -⟩ := h44
  obtain ⟨hUC, hUp, hUmax, hBsU⟩ := h45
  have hdD : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hDd]; exact Subgroup.mem_zpowers d
  have hcanK := hcan X hX1 hX2 hX3 hX4 hX5 d hdD hd1 y K hNbr hyd
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set N := Subgroup.normalizer (K : Set G) with hN
  have hCK : Subgroup.centralizer (B₁ : Set G) ≤ N := by
    intro g hg
    refine hcanK ⟨Subgroup.centralizer_le_normalizer _ hg, ?_⟩
    have hzle : Subgroup.zpowers d ≤ B₁ := by
      rw [Subgroup.zpowers_le]; exact hdD.2
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hzle hg)
  have hU₁K : U₁ ≤ N := hID.2.1.trans hID.1
  set Q := ⁅N, N⁆ ⊔ U₁ with hQ
  have hNN : ⁅N, N⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem h₁ h₂) (N.inv_mem h₁)) (N.inv_mem h₂)
  have hQN : Q ≤ N := sup_le hNN hU₁K
  have hnorm : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q := by
    intro n hn q hq
    have e : n * q * n⁻¹ = ⁅n, q⁆ * q := by rw [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hn (hQN hq))) hq
  have hxU : x ∈ U := hBsU (by rw [h43.2]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hxN : x ∈ N := hCK (hUC hxU)
  have hxp : ∃ k : ℕ, x ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hUp ⟨x, hxU⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxQ : x ∉ Q := hF G p B Bs x L D J X B₂ d y K U U₁ hS
  have hBN : L ⊓ Subgroup.centralizer (B₁ : Set G) ≤ N := inf_le_right.trans hCK
  have hB : ∀ c ∈ L ⊓ Subgroup.centralizer (B₁ : Set G), (∃ k : ℕ, c ^ p ^ k = 1) → c ∈ Q := by
    intro c hc hcp
    obtain ⟨S, W, hSp, hSC, hSJ, hWN, hcl⟩ := hT G p B Bs x L D J X B₂ d y K U U₁ hS hI1 c hc hcp
    exact GGL48TW.mem_commutator_sup_of_weyl hUC hUp
      (fun R hRC hRp hUR => hUmax R hRC hRp hUR) hNU hCK hU₁K hUK hSp hSC (hSJ.trans hJK) hWN hcl
  have hmain := GGL48TW.not_mem_sup_of_pElement_mem hQN hnorm hBN hxN hxp hxQ hB
  have h1 : ⁅Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (B₁ : Set G),
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (B₁ : Set G)⁆ ≤ Q :=
    (Subgroup.commutator_mono (inf_le_right.trans hCK) (inf_le_right.trans hCK)).trans
      le_sup_left
  have h2 : ggL48U2 x U₁ ≤ Q := fun g hg => Subgroup.mem_sup_right hg.1
  have hle := sup_le_sup_right (sup_le h1 h2) (L ⊓ Subgroup.centralizer (B₁ : Set G))
  exact fun hx => hmain (hle hx)

end CFSG.StandardType
