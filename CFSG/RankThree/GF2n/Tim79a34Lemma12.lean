module

public import CFSG.RankThree.GF2n.Tim79a34Local
public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim79a34TwStruct

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem l12_two_elt [Finite G] {K : Subgroup G} (hK : Nat.card K = 2) {g : G}
    (hg : g ∈ K) (hg1 : g ≠ 1) : ∀ x ∈ K, x = 1 ∨ x = g := by
  have hcard : (K : Set G).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hK
  have hsub : ({1, g} : Set G) ⊆ (K : Set G) := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact K.one_mem
    · rw [Set.mem_singleton_iff.mp h]
      exact hg
  have heq : ({1, g} : Set G) = (K : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair (Ne.symm hg1)])
  intro x hx
  have hx' : x ∈ ({1, g} : Set G) := by
    rw [heq]
    exact hx
  rcases Set.mem_insert_iff.mp hx' with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mp h)

theorem l12_le_normalizer {A K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ v ∈ A, k * v * k⁻¹ = v) : K ≤ Subgroup.normalizer (A : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hK k hk h hh]
    exact hh
  · intro hh
    have e := hK k⁻¹ (K.inv_mem hk) _ hh
    have e2 : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
    rw [e2] at e
    rw [e]
    exact hh

theorem l12_conj_comm {P M : Subgroup G} (hM : M ≤ Subgroup.normalizer (P : Set G)) :
    ∀ m ∈ M, ∀ z ∈ ⁅P, P⁆, m * z * m⁻¹ ∈ ⁅P, P⁆ := by
  intro m hm
  have hle : ⁅P, P⁆ ≤ (⁅P, P⁆ : Subgroup G).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap]
    show m * ⁅x, y⁆ * m⁻¹ ∈ ⁅P, P⁆
    have hx' : m * x * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hM hm) x).mp hx
    have hy' : m * y * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hM hm) y).mp hy
    have e : m * ⁅x, y⁆ * m⁻¹ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator hx' hy'
  intro z hz
  exact hle hz

theorem l12_sup_normalizes {P C A : Subgroup G}
    (hP : P ≤ Subgroup.normalizer (A : Set G)) (hC : C ≤ Subgroup.normalizer (A : Set G))
    (hPP : ∀ p ∈ P, ∀ x ∈ P, ⁅p, x⁆ ∈ A) (hPC : ∀ p ∈ P, ∀ c ∈ C, ⁅p, c⁆ ∈ A) :
    ∀ x ∈ P ⊔ C, ∀ p ∈ P, ⁅p, x⁆ ∈ A := by
  let R : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (A : Set G) ∧ ∀ p ∈ P, ⁅p, x⁆ ∈ A}
      one_mem' := ⟨Subgroup.one_mem _, fun p _ => by
        rw [commutatorElement_one_right]
        exact A.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨mul_mem hx hy, fun p hp => ?_⟩
        have e : ⁅p, x * y⁆ = ⁅p, x⁆ * (x * ⁅p, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact A.mul_mem (hx' p hp) ((Subgroup.mem_normalizer_iff.mp hx _).mp (hy' p hp))
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨inv_mem hx, fun p hp => ?_⟩
        have e : ⁅p, x⁻¹⁆ = x⁻¹ * ⁅p, x⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 : ⁅p, x⁆⁻¹ ∈ A := A.inv_mem (hx' p hp)
        have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) _).mp h1
        rwa [inv_inv] at h2 }
  have hPR : P ≤ R := fun x hx => show x ∈ Subgroup.normalizer (A : Set G) ∧
      ∀ p ∈ P, ⁅p, x⁆ ∈ A from ⟨hP hx, fun p hp => hPP p hp x hx⟩
  have hCR : C ≤ R := fun c hc => show c ∈ Subgroup.normalizer (A : Set G) ∧
      ∀ p ∈ P, ⁅p, c⁆ ∈ A from ⟨hC hc, fun p hp => hPC p hp c hc⟩
  intro x hx p hp
  obtain ⟨-, h2⟩ := show x ∈ R from sup_le hPR hCR hx
  exact h2 p hp

theorem lemma12_holds (hIW : Sec34IWStatement) (hγ : Sec34GammaStatement)
    (h11a : Lemma11aStatement) (h11b : Lemma11bStatement) (h11c : Lemma11cStatement) :
    Lemma12Statement := by
  intro G _ _ M V Q P H hH hZ n Φ ψ hNat a T ha hT hTV
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ
  obtain ⟨hcomm', -, hPcent⟩ := h11b G M V Q P H hH hZ hcP
  obtain ⟨hPiff, hRbar, hxOf, hPcard⟩ :=
    h11a G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV
  obtain ⟨C, hCQ, hPCQ, hPC, hCW, -, -⟩ := hγ G M V Q P H hH hZ
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hQn : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
    intro m hm q hq
    rw [hc.hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two M).2.2 hm) q).mp hq
  have hQp : IsPGroup 2 Q := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).1
  have hPQ : P ≤ Q := hc.P_le_Q
  have hPM : P ≤ H := hc.PleH
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      apply ha
      funext i
      rcases i with i | i <;> exact i.elim0
    · omega
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1' : n = 1 := by omega
    subst hn1'
    have h4 : Nat.card ↥P = 4 := by
      rw [hPcard]
      norm_num
    have hPc : IsMulCommutative ↥P :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
    have hPle : P ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hPc
    have hbot : ⁅P, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPle
    have h1 : Nat.card ↥(⁅P, P⁆ : Subgroup G) = 2 := hcomm' ▸ hVWcard
    rw [hbot, Subgroup.card_bot] at h1
    norm_num at h1
  obtain ⟨aG, haG⟩ : ∃ g : G, g = ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) := ⟨_, rfl⟩
  rw [← haG]
  have haW : aG ∈ wOf V H := by
    rw [haG]
    exact (Additive.toMul (ψ a)).2
  have haV : aG ∈ V := by
    rw [haG]
    exact hNat.point a T ha hT hTV
  have hψinj : ∀ c c' : Fin n ⊕ Fin n → GaloisField 2 1,
      ((Additive.toMul (ψ c) : ↥(wOf V H)) : G) = ((Additive.toMul (ψ c') : ↥(wOf V H)) : G) →
        c = c' := by
    intro c c' h
    apply ψ.injective
    apply Additive.toMul.injective
    exact Subtype.ext h
  have hι0 : ((Additive.toMul (ψ 0) : ↥(wOf V H)) : G) = 1 := by
    simp
  have haG1 : aG ≠ 1 := by
    intro h
    apply ha
    apply hψinj a 0
    rw [← haG, h, hι0]
  have haK : aG ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨haV, haW⟩
  have hK0p : IsPGroup 2 (V ⊓ wOf V H : Subgroup G) := hc.isPGroup_V.to_le inf_le_left
  have hK0ne : (V ⊓ wOf V H : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVWcard
    norm_num at hVWcard
  have hconjK := l12_conj_comm hc.M_le_normalizer_P
  rw [hcomm'] at hconjK
  have hMK0 : M ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjK m hm h hh
    · intro hh
      have e := hconjK m⁻¹ (inv_mem hm) _ hh
      have e2 : m⁻¹ * (m * h * m⁻¹) * m⁻¹⁻¹ = h := by group
      rw [e2] at e
      exact e
  have hNM : Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) = M := by
    by_contra hne
    exact hc.maxLocal.2 _ (lt_of_le_of_ne hMK0 (Ne.symm hne)) ⟨V ⊓ wOf V H, hK0ne, hK0p, rfl⟩
  have hcon : ∀ k : G, k * aG = aG * k → ∀ h ∈ (V ⊓ wOf V H : Subgroup G),
      k * h * k⁻¹ ∈ (V ⊓ wOf V H : Subgroup G) := by
    intro k hk h hh
    rcases l12_two_elt hVWcard haK haG1 h hh with h1 | h1
    · rw [h1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [h1, hk, mul_inv_cancel_right]
      exact haK
  have hcentM : Subgroup.centralizer ({aG} : Set G) = M := by
    apply le_antisymm
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff] at hk
      rw [← hNM, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact hcon k hk h hh
      · intro hh
        have hk' : k⁻¹ * aG = aG * k⁻¹ := by
          calc k⁻¹ * aG = k⁻¹ * (aG * k) * k⁻¹ := by group
            _ = k⁻¹ * (k * aG) * k⁻¹ := by rw [hk]
            _ = aG * k⁻¹ := by group
        have e := hcon k⁻¹ hk' _ hh
        have e2 : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
        rw [e2] at e
        exact e
    · intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hNM] at hm
      have h1 : m * aG * m⁻¹ ∈ (V ⊓ wOf V H : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hm aG).mp haK
      rcases l12_two_elt hVWcard haK haG1 _ h1 with h2 | h2
      · exfalso
        apply haG1
        calc aG = m⁻¹ * (m * aG * m⁻¹) * m := by group
          _ = 1 := by rw [h2]; group
      · exact mul_inv_eq_iff_eq_mul.mp h2
  have hXM : xOf V H ⊓ Subgroup.centralizer ({aG} : Set G) ≤ M := by
    rw [hcentM]
    exact inf_le_right
  have hcentX : ∀ x : ↥(xOf V H),
      SpExtras.mat n (GaloisField 2 1) (Φ.symm (xToXbar hVH x)) *ᵥ a = a ↔ (x : G) ∈ M := by
    intro x
    have key := hNat.equiv x a
    constructor
    · intro h
      rw [h, ← haG] at key
      rw [← hcentM, Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * aG = (x : G) * aG * (x : G)⁻¹ * (x : G) := by group
        _ = aG * (x : G) := by rw [← key]
    · intro hx
      rw [← hcentM, Subgroup.mem_centralizer_singleton_iff] at hx
      apply hψinj
      rw [key, ← haG, hx, mul_inv_cancel_right]
  have hNtA : ∀ g ∈ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))),
      SpExtras.mat n (GaloisField 2 1) g *ᵥ a = a := by
    intro g hg
    rw [normalizer_eq_spLine ha hT] at hg
    obtain ⟨μ, hμ, hμa⟩ := hg
    rw [tw_eq_one_of_card_two hF2 hμ, one_smul] at hμa
    exact hμa
  have hNtmem : ∀ g : ↥(StatedSp n (GaloisField 2 1)),
      SpExtras.mat n (GaloisField 2 1) g *ᵥ a = a →
        g ∈ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))) := by
    intro g hg
    rw [normalizer_eq_spLine ha hT]
    exact ⟨1, one_ne_zero, by rw [hg, one_smul]⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup (Xbar V H),
      Y = ((Q ⊓ xOf V H).subgroupOf (xOf V H)).map (xToXbar hVH) := ⟨_, rfl⟩
  have hYmem : ∀ z : Xbar V H, z ∈ Y ↔
      ∃ x : ↥(xOf V H), (x : G) ∈ Q ⊓ xOf V H ∧ xToXbar hVH x = z := by
    intro z
    rw [hY, Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup ↥(StatedSp n (GaloisField 2 1)),
      S = Y.comap Φ.toMonoidHom := ⟨_, rfl⟩
  have hSmem : ∀ g : ↥(StatedSp n (GaloisField 2 1)), g ∈ S ↔ Φ g ∈ Y := by
    intro g
    rw [hS, Subgroup.mem_comap]
    exact Iff.rfl
  have hSN : S ≤ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))) := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := (hYmem _).mp ((hSmem g).mp hg)
    have hxM : (x : G) ∈ M := hQM (Subgroup.mem_inf.mp hx).1
    have hσ := (hcentX x).mpr hxM
    have hgx : Φ.symm (xToXbar hVH x) = g := by
      rw [hxg]
      exact Φ.symm_apply_apply g
    rw [hgx] at hσ
    exact hNtmem g hσ
  have hSnorm : ∀ n₁ ∈ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))),
      ∀ s ∈ S, n₁ * s * n₁⁻¹ ∈ S := by
    intro n₁ hn₁ s hs
    obtain ⟨x, hxn⟩ := xToXbar_surjective hVH (Φ n₁)
    have hxn' : Φ.symm (xToXbar hVH x) = n₁ := by
      rw [hxn]
      exact Φ.symm_apply_apply n₁
    have hxM : (x : G) ∈ M := (hcentX x).mp (by
      rw [hxn']
      exact hNtA n₁ hn₁)
    obtain ⟨y, hy, hys⟩ := (hYmem _).mp ((hSmem s).mp hs)
    apply (hSmem _).mpr
    rw [hYmem]
    refine ⟨x * y * x⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_inf.mpr ⟨hQn x hxM y (Subgroup.mem_inf.mp hy).1, (x * y * x⁻¹).2⟩
    · simp only [map_mul, map_inv]
      rw [hxn, hys]
  have hSnorm' : Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))) ≤
      Subgroup.normalizer (S : Set ↥(StatedSp n (GaloisField 2 1))) := by
    intro n₁ hn₁
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact hSnorm n₁ hn₁ s
    · intro hs
      have h1 := hSnorm n₁⁻¹ (inv_mem hn₁) _ hs
      have e : n₁⁻¹ * (n₁ * s * n₁⁻¹) * n₁⁻¹⁻¹ = s := by group
      rw [e] at h1
      exact h1
  have hSp : IsPGroup 2 S := by
    intro g
    obtain ⟨y, hy, hyg⟩ := (hYmem _).mp ((hSmem g.1).mp g.2)
    obtain ⟨k, hk⟩ := hQp ⟨(y : G), (Subgroup.mem_inf.mp hy).1⟩
    have hyk : (y : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hyk' : y ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
    have hgk : (g.1 : ↥(StatedSp n (GaloisField 2 1))) ^ 2 ^ k = 1 := by
      apply Φ.injective
      rw [map_pow, ← hyg, ← map_pow, hyk', map_one, map_one]
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hgk
  have hSspRad : S ≤ spRad a := by
    rw [← spCoreStmt_holds n (GaloisField 2 1) ha hT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSN hSnorm' hSp
  have hyR : ∀ y : ↥(xOf V H), (y : G) ∈ Q → xToXbar hVH y ∈ Rbar V H P := by
    intro y hyQ
    have hyS : Φ.symm (xToXbar hVH y) ∈ S := by
      rw [hSmem, Φ.apply_symm_apply]
      exact (hYmem _).mpr ⟨y, Subgroup.mem_inf.mpr ⟨hyQ, y.2⟩, rfl⟩
    have hsp := hSspRad hyS
    rw [hRbar]
    exact Subgroup.mem_map.mpr ⟨Φ.symm (xToXbar hVH y), hsp, by simp⟩
  have hPR : ∀ x ∈ Q, ∀ p ∈ P, ⁅p, x⁆ ∈ (V ⊓ wOf V H : Subgroup G) := by
    have hPcentA : ∀ p ∈ P, ∀ v ∈ (V ⊓ wOf V H : Subgroup G), p * v * p⁻¹ = v := by
      intro p hp v hv
      have hcent : v ∈ Subgroup.centralizer (P : Set G) := by
        rw [hPcent]
        exact (Subgroup.mem_inf.mp hv).1
      have hpv := Subgroup.mem_centralizer_iff.mp hcent p hp
      rw [hpv, mul_inv_cancel_right]
    have hCcentA : ∀ c ∈ C, ∀ v ∈ (V ⊓ wOf V H : Subgroup G), c * v * c⁻¹ = v := by
      intro c hc' v hv
      rw [hCW c hc' v (Subgroup.mem_inf.mp hv).2, mul_inv_cancel_right]
    have hPN : P ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
      l12_le_normalizer hPcentA
    have hCN : C ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
      l12_le_normalizer hCcentA
    have hPPc : ∀ p ∈ P, ∀ x ∈ P, ⁅p, x⁆ ∈ (V ⊓ wOf V H : Subgroup G) := by
      intro p hp x hx
      have := Subgroup.commutator_mem_commutator hp hx
      rwa [hcomm'] at this
    have key := l12_sup_normalizes hPN hCN hPPc hPC
    intro x hx
    rw [← hPCQ] at hx
    exact key x hx
  have hWQ : ∀ w ∈ wOf V H, w ∈ Q → w ∈ P := by
    intro w hwW hwQ
    by_contra hwP
    obtain ⟨b, hbw⟩ : ∃ b : Fin n ⊕ Fin n → GaloisField 2 1,
        ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) = w :=
      ⟨ψ.symm (Additive.ofMul ⟨w, hwW⟩), by
        rw [AddEquiv.apply_symm_apply]
        rfl⟩
    have hbP : CaseM.spForm a b ≠ 0 := fun h => hwP (hbw ▸ (hPiff b).mpr h)
    have hb1 : CaseM.spForm a b = 1 := tw_eq_one_of_card_two hF2 hbP
    have hcov := (h11c G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV b hb1).2
    have hPWsub : ∀ u ∈ P ⊓ wOf V H, u ∈ V ⊓ wOf V H := by
      intro u hu
      obtain ⟨p, hp, hpu⟩ := hcov u hu
      rw [hbw] at hpu
      rw [← hpu]
      exact hPR w hwQ p hp
    have hcount : ∀ c : Fin n ⊕ Fin n → GaloisField 2 1,
        CaseM.spForm a c = 0 → c = 0 ∨ c = a := by
      intro c hc0
      have hmem : ((Additive.toMul (ψ c) : ↥(wOf V H)) : G) ∈ V ⊓ wOf V H :=
        hPWsub _ (Subgroup.mem_inf.mpr ⟨(hPiff c).mpr hc0, (Additive.toMul (ψ c)).2⟩)
      rcases l12_two_elt hVWcard haK haG1 _ hmem with h1 | h1
      · left
        apply hψinj
        rw [h1, hι0]
      · right
        apply hψinj
        rw [h1, haG]
    have hsub2 : {c : Fin n ⊕ Fin n → GaloisField 2 1 | CaseM.spForm a c = 0} ⊆
        ({0, a} : Set (Fin n ⊕ Fin n → GaloisField 2 1)) := by
      intro c hc0
      rcases hcount c hc0 with h | h
      · rw [h]
        exact Set.mem_insert _ _
      · rw [h]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hKcard : Nat.card ↥(LinearMap.ker (spFormL a)) = 2 ^ (2 * n - 1) := by
      rw [natCard_ker_spFormL ha, hF2]
    have hncard : Set.ncard {c : Fin n ⊕ Fin n → GaloisField 2 1 | CaseM.spForm a c = 0} =
        2 ^ (2 * n - 1) := by
      rw [← Nat.card_coe_set_eq, ← hKcard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
        (LinearMap.mem_ker (f := spFormL a) (y := w)).symm)
    have hle : Set.ncard {c : Fin n ⊕ Fin n → GaloisField 2 1 | CaseM.spForm a c = 0} ≤ 2 := by
      calc Set.ncard {c : Fin n ⊕ Fin n → GaloisField 2 1 | CaseM.spForm a c = 0}
          ≤ Set.ncard ({0, a} : Set (Fin n ⊕ Fin n → GaloisField 2 1)) :=
            Set.ncard_le_ncard hsub2 (Set.toFinite _)
        _ = 2 := Set.ncard_pair (Ne.symm ha)
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hncard] at hle
    exact absurd (le_trans h8 hle) (by norm_num)
  have hWQeq : wOf V H ⊓ Q = P ⊓ wOf V H := by
    apply le_antisymm
    · intro w hw
      exact Subgroup.mem_inf.mpr ⟨hWQ w (Subgroup.mem_inf.mp hw).1 (Subgroup.mem_inf.mp hw).2,
        (Subgroup.mem_inf.mp hw).1⟩
    · intro w hw
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).2, hPQ (Subgroup.mem_inf.mp hw).1⟩
  have hQXP : ∀ y : ↥(xOf V H), (y : G) ∈ Q → (y : G) ∈ P := by
    intro y hyQ
    obtain ⟨x, hxP, hxeq⟩ := mem_barOf_iff.mp (mem_Rbar.mp (hyR y hyQ))
    rw [coe_xToXbar] at hxeq
    have hw : (x : G)⁻¹ * (y : G) ∈ wOf V H := by
      have h1 : piBar V H (x⁻¹ * Subgroup.inclusion (xOf_le_H hVH) y) = 1 := by
        rw [map_mul, map_inv, hxeq, inv_mul_cancel]
      exact (piBar_eq_one_iff _).mp h1
    have hxQ : (x : G) ∈ Q := hPQ hxP
    have hwQ : (x : G)⁻¹ * (y : G) ∈ Q := Q.mul_mem (Q.inv_mem hxQ) hyQ
    have hwP := hWQ _ hw hwQ
    have e : (y : G) = (x : G) * ((x : G)⁻¹ * (y : G)) := by group
    rw [e]
    exact P.mul_mem hxP hwP
  have hQX : Q ⊓ xOf V H = P := by
    apply le_antisymm
    · intro z hz
      exact hQXP ⟨z, (Subgroup.mem_inf.mp hz).2⟩ (Subgroup.mem_inf.mp hz).1
    · intro p hp
      refine Subgroup.mem_inf.mpr ⟨hPQ hp, ?_⟩
      rw [hxOf]
      exact hPM hp
  have hMW : ¬ M ≤ Subgroup.normalizer (wOf V H : Set G) := by
    intro hMW'
    have hWne : wOf V H ≠ ⊥ := by
      intro h
      obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
      have hbW : ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) ∈ (⊥ : Subgroup G) := by
        rw [← h]
        exact (Additive.toMul (ψ b)).2
      rw [Subgroup.mem_bot] at hbW
      have hb0 : b = 0 := hψinj b 0 (hbW.trans hι0.symm)
      rw [hb0, spForm_zero_right] at hb
      exact zero_ne_one hb
    have hWp : IsPGroup 2 (wOf V H : Subgroup G) :=
      isPGroup_two_of_isElemAbelian (MinCex.wOf_isElemAbelian hc)
    have hNW : Subgroup.normalizer (wOf V H : Set G) = M := by
      by_contra hne
      exact hc.maxLocal.2 _ (lt_of_le_of_ne hMW' (Ne.symm hne)) ⟨wOf V H, hWne, hWp, rfl⟩
    have hWM : wOf V H ≤ M := by
      have := (Subgroup.le_normalizer (H := wOf V H))
      rwa [hNW] at this
    have hWQ' : wOf V H ≤ Q := by
      rw [hc.hQ]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWM hMW' hWp
    obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
    have hbW : ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) ∈ wOf V H :=
      (Additive.toMul (ψ b)).2
    have hbP := hWQ _ hbW (hWQ' hbW)
    have hb0 := (hPiff b).mp hbP
    rw [hb] at hb0
    exact one_ne_zero hb0
  exact ⟨hcentM, hXM, hQX, hWQeq, hMW⟩

end CFSG.RankThree.GF2n.Tim79a
