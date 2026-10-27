module

public import CFSG.Quasithin.H13.A6S13833g

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped Pointwise

@[expose] def tau0213 : Perm (Fin 6) := swap 0 2 * swap 1 3

theorem card_centralizer_tau0213 :
    Nat.card (Subgroup.centralizer ({tau0213} : Set (Perm (Fin 6)))) = 16 := by
  have e : Nat.card (Subgroup.centralizer ({tau0213} : Set (Perm (Fin 6)))) =
      (Finset.univ.filter fun σ : Perm (Fin 6) => σ * tau0213 = tau0213 * σ).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
      rw [Finset.mem_filter, Subgroup.mem_centralizer_singleton_iff]
      simp)
  rw [e]
  decide +kernel

theorem centralizer_tau0213_noncomm :
    swap (0 : Fin 6) 2 * tau0213 = tau0213 * swap 0 2 ∧
      (swap (0 : Fin 6) 1 * swap 2 3) * tau0213 = tau0213 * (swap 0 1 * swap 2 3) ∧
      swap (0 : Fin 6) 2 * (swap 0 1 * swap 2 3) ≠ (swap 0 1 * swap 2 3) * swap 0 2 := by
  decide

theorem card_le_eight_of_elem {E : Subgroup (Perm (Fin 6))}
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := by
    rintro ⟨a, ha⟩
    exact ⟨1, Subtype.ext (by simp [pow_one, sq, h2 a ha])⟩
  have h720 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have hle16 : ∀ X : Subgroup (Perm (Fin 6)), IsPGroup 2 X → Nat.card X ≤ 16 := by
    intro X hX
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hX
    have hd : 2 ^ m ∣ 720 := hm ▸ h720 ▸ Subgroup.card_subgroup_dvd_card X
    have hm4 : m ≤ 4 := by
      by_contra h
      push Not at h
      have : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 h).trans hd
      norm_num at this
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm4
      _ = 16 := by norm_num
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  by_contra hgt
  push Not at hgt
  have h16 : Nat.card E = 16 := by
    have h1 := hle16 E hp
    rw [hn] at h1 hgt ⊢
    have hn3 : 3 < n := by
      by_contra h
      push Not at h
      have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h
      omega
    have hn4 : n ≤ 4 := by
      by_contra h
      push Not at h
      have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      omega
    have : n = 4 := by omega
    rw [this]; norm_num
  set C₀ := Subgroup.centralizer ({tau0213} : Set (Perm (Fin 6))) with hC₀
  have hC₀p : IsPGroup 2 C₀ :=
    IsPGroup.of_card (card_centralizer_tau0213.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
  obtain ⟨P, hEP⟩ := hp.exists_le_sylow
  obtain ⟨P₀, hCP⟩ := hC₀p.exists_le_sylow
  have hPE : (P : Subgroup (Perm (Fin 6))) = E :=
    (Subgroup.eq_of_le_of_card_ge hEP (by rw [h16]; exact hle16 _ P.isPGroup')).symm
  have hP₀C : (P₀ : Subgroup (Perm (Fin 6))) = C₀ :=
    (Subgroup.eq_of_le_of_card_ge hCP (by
      rw [card_centralizer_tau0213]; exact hle16 _ P₀.isPGroup')).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) P₀ P
  have hmem : ∀ a ∈ C₀, g * a * g⁻¹ ∈ E := by
    intro a ha
    rw [← hPE, ← hg, Sylow.coe_subgroup_smul, hP₀C]
    exact Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.2 ⟨a, ha, rfl⟩
  obtain ⟨h1, h2', h3⟩ := centralizer_tau0213_noncomm
  have ha : swap (0 : Fin 6) 2 ∈ C₀ := Subgroup.mem_centralizer_singleton_iff.2 h1
  have hb : swap (0 : Fin 6) 1 * swap 2 3 ∈ C₀ := Subgroup.mem_centralizer_singleton_iff.2 h2'
  have := hab _ (hmem _ ha) _ (hmem _ hb)
  apply h3
  have e : g * swap 0 2 * g⁻¹ * (g * (swap 0 1 * swap 2 3) * g⁻¹) =
      g * (swap 0 2 * (swap 0 1 * swap 2 3)) * g⁻¹ := by group
  have e' : g * (swap 0 1 * swap 2 3) * g⁻¹ * (g * swap 0 2 * g⁻¹) =
      g * ((swap 0 1 * swap 2 3) * swap 0 2) * g⁻¹ := by group
  rw [e, e'] at this
  simpa using this

@[expose] def zpw {G : Type} [Group G] (e : ZMod 2) (w : G) : G := if e = 1 then w else 1

theorem zpw_add {G : Type} [Group G] {w : G} (hw : w * w = 1) (a b : ZMod 2) :
    zpw (a + b) w = zpw a w * zpw b w := by
  rcases zmod2_cases' a with rfl | rfl <;> rcases zmod2_cases' b with rfl | rfl <;>
    simp [zpw, hw]

theorem zpw_mem {G : Type} [Group G] {A : Subgroup G} {w : G} (hw : w ∈ A) (e : ZMod 2) :
    zpw e w ∈ A := by
  unfold zpw; split_ifs
  · exact hw
  · exact A.one_mem

@[expose] def prod4 {G : Type} [Group G] (w : Fin 4 → G) (ε : Fin 4 → ZMod 2) : G :=
  zpw (ε 0) (w 0) * zpw (ε 1) (w 1) * zpw (ε 2) (w 2) * zpw (ε 3) (w 3)

theorem exists_prod4_mem {G : Type} [Group G] [Finite G] {A V : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A ≤ 16) {v : G} (hvA : v ∈ A) (hvV : v ∈ V) (hv1 : v ≠ 1)
    {w : Fin 4 → G} (hw : ∀ i, w i ∈ A) :
    ∃ ε : Fin 4 → ZMod 2, ε ≠ 0 ∧ prod4 w ε ∈ V := by
  classical
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hAab a a.2 b b.2) }
  let wA : Fin 4 → ↥A := fun i => ⟨w i, hw i⟩
  let W : (Fin 4 → ZMod 2) → ↥A := fun ε => ∏ i, zpw (ε i) (wA i)
  have hW : ∀ ε, (W ε : G) = prod4 w ε := by
    intro ε
    simp only [W, Fin.prod_univ_four, Subgroup.coe_mul]
    unfold prod4 zpw
    split_ifs <;> rfl
  have hWadd : ∀ ε ε', W (ε + ε') = W ε * W ε' := by
    intro ε ε'
    simp only [W, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact zpw_add (Subtype.ext (hA2 _ (hw i))) _ _
  let B : Subgroup ↥A := V.subgroupOf A
  let Ψ : (Fin 4 → ZMod 2) × ↥B → ↥A := fun p => W p.1 * p.2
  have hnot : ¬ Function.Injective Ψ := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective Ψ hinj
    rw [Nat.card_prod] at h1
    have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
      rw [Nat.card_eq_fintype_card]; rfl
    have h2 : 2 ≤ Nat.card ↥B := by
      have hb : (⟨⟨v, hvA⟩, by simpa [B, Subgroup.mem_subgroupOf] using hvV⟩ : ↥B) ≠ 1 := by
        intro h
        exact hv1 (congrArg (fun x : ↥B => ((x : ↥A) : G)) h)
      have : Nontrivial ↥B := ⟨⟨_, 1, hb⟩⟩
      exact Finite.one_lt_card
    rw [h16] at h1
    omega
  rw [Function.Injective] at hnot
  push Not at hnot
  obtain ⟨⟨ε, b⟩, ⟨ε', b'⟩, he, hne⟩ := hnot
  have he' : W ε * (b : ↥A) = W ε' * (b' : ↥A) := he
  refine ⟨ε + ε', ?_, ?_⟩
  · intro h0
    apply hne
    have hεε : ε = ε' := by
      funext i
      have := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      rcases zmod2_cases' (ε i) with h | h <;> rcases zmod2_cases' (ε' i) with h' | h' <;>
        rw [h, h'] at this ⊢ <;> first | rfl | exact absurd this (by decide)
    subst hεε
    have hbb : (b : ↥A) = b' := mul_left_cancel he'
    exact Prod.ext rfl (Subtype.ext hbb)
  · have hsq : ∀ y : ↥A, y * y = 1 := fun y => Subtype.ext (hA2 _ y.2)
    have key : W (ε + ε') = (b' : ↥A) * (b : ↥A)⁻¹ := by
      rw [hWadd]
      calc W ε * W ε' = W ε * (b : ↥A) * (b : ↥A)⁻¹ * W ε' := by group
        _ = W ε' * (b' : ↥A) * (b : ↥A)⁻¹ * W ε' := by rw [he']
        _ = (W ε' * W ε') * ((b' : ↥A) * (b : ↥A)⁻¹) := by
          rw [mul_comm (W ε' * (b' : ↥A) * (b : ↥A)⁻¹) (W ε')]; group
        _ = (b' : ↥A) * (b : ↥A)⁻¹ := by rw [hsq, one_mul]
    rw [← hW, key]
    have hb : ((b : ↥A) : G) ∈ V := b.2
    have hb' : ((b' : ↥A) : G) ∈ V := b'.2
    show ((b' : ↥A) : G) * ((b : ↥A) : G)⁻¹ ∈ V
    exact V.mul_mem hb' (V.inv_mem hb)

theorem comm_mul_of_comm {G : Type} [Group G] {q a b : G}
    (hc : a * (q * b * q⁻¹ * b⁻¹) = (q * b * q⁻¹ * b⁻¹) * a) :
    q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by
  calc q * (a * b) * q⁻¹ * (a * b)⁻¹ =
      (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹)) * a⁻¹ := by group
    _ = (q * a * q⁻¹ * a⁻¹) * ((q * b * q⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [hc]
    _ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by group

theorem comm_inv_of_comm {G : Type} [Group G] {q b : G}
    (hc : b * (q * b * q⁻¹ * b⁻¹) = (q * b * q⁻¹ * b⁻¹) * b) :
    q * b⁻¹ * q⁻¹ * b⁻¹⁻¹ = (q * b * q⁻¹ * b⁻¹)⁻¹ := by
  have hc' : (q * b * q⁻¹ * b⁻¹)⁻¹ * b = b * (q * b * q⁻¹ * b⁻¹)⁻¹ := by
    calc (q * b * q⁻¹ * b⁻¹)⁻¹ * b =
        (q * b * q⁻¹ * b⁻¹)⁻¹ * (b * (q * b * q⁻¹ * b⁻¹)) * (q * b * q⁻¹ * b⁻¹)⁻¹ := by group
      _ = (q * b * q⁻¹ * b⁻¹)⁻¹ * ((q * b * q⁻¹ * b⁻¹) * b) * (q * b * q⁻¹ * b⁻¹)⁻¹ := by
          rw [hc]
      _ = b * (q * b * q⁻¹ * b⁻¹)⁻¹ := by group
  calc q * b⁻¹ * q⁻¹ * b⁻¹⁻¹ = b⁻¹ * ((q * b * q⁻¹ * b⁻¹)⁻¹ * b) := by group
    _ = b⁻¹ * (b * (q * b * q⁻¹ * b⁻¹)⁻¹) := by rw [hc']
    _ = (q * b * q⁻¹ * b⁻¹)⁻¹ := by group

theorem comm_zpw {G : Type} [Group G] (q w : G) (e : ZMod 2) :
    q * zpw e w * q⁻¹ * (zpw e w)⁻¹ = zpw e (q * w * q⁻¹ * w⁻¹) := by
  unfold zpw; split_ifs
  · rfl
  · group

theorem ConI_rEps_iff (ε : Fin 4 → ZMod 2) (t : Fin 15 → ZMod 2) :
    ConI (rEps ε) t ↔ ∑ i : Fin 4, ε i • (t (![3, 7, 10, 12] i) • dA (![3, 7, 10, 12] i) +
      t (![4, 8, 11, 13] i) • dA (![4, 8, 11, 13] i)) = 0 := by
  have e : ∑ k, (rEps ε k * t k) • dA k = ∑ i : Fin 4, ε i • (t (![3, 7, 10, 12] i) •
      dA (![3, 7, 10, 12] i) + t (![4, 8, 11, 13] i) • dA (![4, 8, 11, 13] i)) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, rEps, smul_add, smul_smul]
    simp
    abel
  unfold ConI
  rw [e]

theorem dPerm_swap45 : ∀ i : Fin 4, dPerm (swap 4 5) (![3, 7, 10, 12] i) = ![4, 8, 11, 13] i := by
  decide +kernel

theorem act4f_swap45_e0123 : act4f (swap 4 5) e0123 = e0123 := by decide

theorem comm_prod4 {G : Type} [Group G] {U : Subgroup G}
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {q : G} {w : Fin 4 → G} (hw : ∀ i, w i ∈ U)
    (hqw : ∀ i, q * w i * q⁻¹ * (w i)⁻¹ ∈ U)
    (ε : Fin 4 → ZMod 2) :
    q * prod4 w ε * q⁻¹ * (prod4 w ε)⁻¹ = prod4 (fun i => q * w i * q⁻¹ * (w i)⁻¹) ε := by
  have hz : ∀ i, zpw (ε i) (w i) ∈ U := fun i => zpw_mem (hw i) _
  have hzc : ∀ i, q * zpw (ε i) (w i) * q⁻¹ * (zpw (ε i) (w i))⁻¹ ∈ U := fun i => by
    rw [comm_zpw]; exact zpw_mem (hqw i) _
  unfold prod4
  rw [comm_mul_of_comm (hUab _ (U.mul_mem (U.mul_mem (hz 0) (hz 1)) (hz 2)) _ (hzc 3)),
    comm_mul_of_comm (hUab _ (U.mul_mem (hz 0) (hz 1)) _ (hzc 2)),
    comm_mul_of_comm (hUab _ (hz 0) _ (hzc 1)), comm_zpw, comm_zpw, comm_zpw, comm_zpw]

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section DBound

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
include hker hUL

theorem relIndex_UL_inf_le_eight {a : G}
    (hA : conjSub a (fsuV1 T V) ≤ conjClosure (conjClosure S.V3 S.G1) L) :
    (conjClosure (conjClosure S.V3 S.G1) L ⊓ conjSub a (pCoreOf 2 S.G1)).relIndex
      (conjClosure (conjClosure S.V3 S.G1) L) ≤ 8 := by
  set UL := conjClosure (conjClosure S.V3 S.G1) L with hULdef
  have hUg : ∀ u : ↥UL, a⁻¹ * (u : G) * a ∈ S.G1 := fun u => S.conj_mem_G1_of_UL hUL hA u.2
  let φ : ↥UL →* Perm (Fin 6) :=
    { toFun := fun u => ρ ⟨a⁻¹ * (u : G) * a, hUg u⟩
      map_one' := by
        have e : (⟨a⁻¹ * ((1 : ↥UL) : G) * a, hUg 1⟩ : ↥S.G1) = 1 := Subtype.ext (by simp)
        simp only [e, map_one]
      map_mul' := fun u v => by
        have e : (⟨a⁻¹ * ((u * v : ↥UL) : G) * a, hUg (u * v)⟩ : ↥S.G1) =
            ⟨a⁻¹ * (u : G) * a, hUg u⟩ * ⟨a⁻¹ * (v : G) * a, hUg v⟩ :=
          Subtype.ext (by simp only [Subgroup.coe_mul]; group)
        simp only [e, map_mul] }
  have hker' : φ.ker = (UL ⊓ conjSub a (pCoreOf 2 S.G1)).subgroupOf UL := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_conjSub]
    constructor
    · intro h
      exact ⟨u.2, (hker _).1 h⟩
    · rintro ⟨-, h⟩
      exact (hker ⟨_, hUg u⟩).2 h
  have hidx : (UL ⊓ conjSub a (pCoreOf 2 S.G1)).relIndex UL = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker', Subgroup.index_ker]
  rw [hidx]
  refine card_le_eight_of_elem (fun σ hσ τ hτ => ?_) (fun σ hσ => ?_)
  · obtain ⟨u, rfl⟩ := hσ
    obtain ⟨v, rfl⟩ := hτ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_comm hUL u.2 v.2)
  · obtain ⟨u, rfl⟩ := hσ
    rw [← map_mul]
    have hu : u * u = 1 := Subtype.ext (by
      have := hUL.2 (u : G) u.2
      rw [sq] at this
      exact this)
    rw [hu, map_one]

theorem relIndex_UL_centralizer_le (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) {a x : G}
    (hA : conjSub a (fsuV1 T V) ≤ conjClosure (conjClosure S.V3 S.G1) L)
    (hx : x ∈ conjSub a (conjClosure S.V3 S.G1)) :
    (conjClosure (conjClosure S.V3 S.G1) L ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
      (conjClosure (conjClosure S.V3 S.G1) L) ≤ 16 := by
  set UL := conjClosure (conjClosure S.V3 S.G1) L with hULdef
  set P := UL ⊓ conjSub a (pCoreOf 2 S.G1) with hPdef
  have hP8 : P.relIndex UL ≤ 8 := S.relIndex_UL_inf_le_eight hker hUL hA
  have hA2 : Nat.card (conjSub a (fsuV1 T V)) = 2 := by
    rw [CosetGeom.card_conjSub, S.card_V1]
  have hAP : conjSub a (fsuV1 T V) ≤ P := le_inf hA (conjSub_mono _ hF.toHypF91.V₁_le_pCoreOf)
  have hcomm : ∀ u ∈ P, x * u * x⁻¹ * u⁻¹ ∈ conjSub a (fsuV1 T V) := fun u hu =>
    S.comm_mem_A1 hF hx hu.2
  have hxP : ∀ u ∈ P, x * u * x⁻¹ ∈ P := fun u hu => by
    have e : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact P.mul_mem (hAP (hcomm u hu)) hu
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    isElemAbelian_comm hUL ha.1 hb.1
  set C := P ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have hC2 : C.relIndex P ≤ 2 := by
    by_cases hne : ∃ u₀ ∈ P, x * u₀ * x⁻¹ * u₀⁻¹ ≠ 1
    · obtain ⟨u₀, hu₀, hne⟩ := hne
      rw [relIndex_centralizer_eq_two hPab hxP hA2 hcomm hu₀ hne]
    · push Not at hne
      have hle : P ≤ C := fun u hu => by
        refine ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 := hne u hu
        calc u * x = (x * u * x⁻¹ * u⁻¹)⁻¹ * (x * u) := by group
          _ = x * u := by rw [h1, inv_one, one_mul]
      rw [Subgroup.relIndex_eq_one.2 hle]
      norm_num
  have hCle : C ≤ UL ⊓ Subgroup.centralizer ({x} : Set G) := inf_le_inf_right _ inf_le_left
  have hpos : C.relIndex UL ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card C UL
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  calc (UL ⊓ Subgroup.centralizer ({x} : Set G)).relIndex UL ≤ C.relIndex UL :=
        Subgroup.relIndex_le_of_le_left hCle hpos
    _ = C.relIndex P * P.relIndex UL :=
        (Subgroup.relIndex_mul_relIndex C P UL inf_le_left inf_le_left).symm
    _ ≤ 2 * 8 := Nat.mul_le_mul hC2 hP8
    _ = 16 := by norm_num

end DBound

@[expose] noncomputable def coordV (y : G) : Fin 6 → ZMod 2 := by
  classical
  exact if h : y ∈ V then Multiplicative.toAdd (S.frame.ψ ⟨y, h⟩ : P6) else 0

theorem coordV_of_mem {y : G} (h : y ∈ V) :
    S.coordV y = Multiplicative.toAdd (S.frame.ψ ⟨y, h⟩ : P6) := by
  unfold coordV; simp [h]

theorem coordV_mul {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    S.coordV (a * b) = S.coordV a + S.coordV b := by
  rw [S.coordV_of_mem (V.mul_mem ha hb), S.coordV_of_mem ha, S.coordV_of_mem hb]
  have e : (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [e, map_mul]
  rfl

theorem coordV_one : S.coordV 1 = 0 := by
  rw [S.coordV_of_mem V.one_mem]
  have e : (⟨1, V.one_mem⟩ : ↥V) = 1 := rfl
  rw [e, map_one]
  rfl

theorem coordV_zpw (c : G) (e : ZMod 2) : S.coordV (zpw e c) = e • S.coordV c := by
  unfold zpw
  rcases zmod2_cases' e with rfl | rfl
  · simp [S.coordV_one]
  · simp

theorem coordV_prod4 {c : Fin 4 → G} (hc : ∀ i, c i ∈ V) (ε : Fin 4 → ZMod 2) :
    S.coordV (prod4 c ε) = ∑ i, ε i • S.coordV (c i) := by
  have hz : ∀ i, zpw (ε i) (c i) ∈ V := fun i => zpw_mem (hc i) _
  unfold prod4
  rw [S.coordV_mul (V.mul_mem (V.mul_mem (hz 0) (hz 1)) (hz 2)) (hz 3),
    S.coordV_mul (V.mul_mem (hz 0) (hz 1)) (hz 2), S.coordV_mul (hz 0) (hz 1),
    S.coordV_zpw (c 0), S.coordV_zpw (c 1), S.coordV_zpw (c 2), S.coordV_zpw (c 3),
    Fin.sum_univ_four]

section Rel

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {u₁ : G} (hu₁ : u₁ ∈ S.U1c β) (hu₁V : u₁ ∉ fsuV1 T V)
  (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
include hker hβk hβe hu₁ hu₁V hUL

theorem exists_rel (h13315 : Stmt13_3_15) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
    (htr : IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V))
    (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1) :
    ∃ ε : Fin 4 → ZMod 2, ε ≠ 0 ∧ ∀ q ∈ pCoreOf 2 (L ⊔ T), ConI (rEps ε) (S.Fq u₁ q) := by
  set UL := conjClosure (conjClosure S.V3 S.G1) L with hULdef
  obtain ⟨x, hxU, hx⟩ := S.exists_Uγ_swap45 h13315 hF s hDH hDγ htr
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hQT := S.pCoreOf_G1_le_T
  rw [hg1] at hQT
  have hxT : (x : G) ∈ T := hQT (S.Uγ_le_QH_case1 hF s hDγ hxU)
  have hxG : (x : G) ∈ S.G1 := by
    have := S.T_le_NV1 hxT
    rwa [S.normalizer_V1] at this
  have hULab : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb => isElemAbelian_comm hUL ha hb
  have hULsq : ∀ a ∈ UL, a * a = 1 := fun a ha => by
    have := hUL.2 a ha
    rwa [sq] at this
  have hxN : (x : G) ∈ Subgroup.normalizer (UL : Set G) := S.LT_le_NUL (Subgroup.mem_sup_right hxT)
  have hxUL : ∀ u ∈ UL, (x : G) * u * (x : G)⁻¹ ∈ UL := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hxN u).mp hu
  have hVUL : V ≤ UL := (S.V_le_U0c hβk).trans S.U0c_le_UL
  let κ : ↥UL →* G :=
    { toFun := fun u => (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have h1 : (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ UL := hxUL _ (UL.inv_mem a.2)
        have h2 : (x : G) * (b : G)⁻¹ * (x : G)⁻¹ ∈ UL := hxUL _ (UL.inv_mem b.2)
        have c1 := hULab _ b.2 _ h1
        have c2 := hULab _ h1 _ h2
        simp only [Subgroup.coe_mul]
        calc (a : G) * b * x * ((a : G) * b)⁻¹ * (x : G)⁻¹ =
            (a : G) * b * (((x : G) * (b : G)⁻¹ * (x : G)⁻¹) *
              ((x : G) * (a : G)⁻¹ * (x : G)⁻¹)) := by group
          _ = (a : G) * b * (((x : G) * (a : G)⁻¹ * (x : G)⁻¹) *
              ((x : G) * (b : G)⁻¹ * (x : G)⁻¹)) := by rw [← c2]
          _ = (a : G) * ((b : G) * ((x : G) * (a : G)⁻¹ * (x : G)⁻¹)) *
              ((x : G) * (b : G)⁻¹ * (x : G)⁻¹) := by group
          _ = (a : G) * (((x : G) * (a : G)⁻¹ * (x : G)⁻¹) * b) *
              ((x : G) * (b : G)⁻¹ * (x : G)⁻¹) := by rw [c1]
          _ = (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ * ((b : G) * x * (b : G)⁻¹ * (x : G)⁻¹) := by
              group }
  set A := κ.range with hAdef
  have hAUL : A ≤ UL := by
    rintro _ ⟨u, rfl⟩
    show (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ ∈ UL
    have e : (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ = (u : G) * ((x : G) * (u : G)⁻¹ * (x : G)⁻¹) := by
      group
    rw [e]
    exact UL.mul_mem u.2 (hxUL _ (UL.inv_mem u.2))
  have hAcard : Nat.card A ≤ 16 := by
    have hk : κ.ker = (UL ⊓ Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf UL := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      show (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ = 1 ↔ (u : G) ∈ UL ∧ (u : G) * x = x * u
      constructor
      · intro h
        refine ⟨u.2, ?_⟩
        calc (u : G) * x = ((u : G) * x * (u : G)⁻¹ * (x : G)⁻¹) * (x * u) := by group
          _ = x * u := by rw [h, one_mul]
      · rintro ⟨-, h⟩
        rw [h]; group
    have h1 : Nat.card A = κ.ker.index := (Subgroup.index_ker κ).symm
    rw [h1, hk]
    exact S.relIndex_UL_centralizer_le hker hUL hF (hA1.trans (le_conjClosure _ L)) hxU
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v ∈ V, (x : G) * v * (x : G)⁻¹ ≠ v := by
    by_contra hall
    push Not at hall
    have h1 : S.frame.ρ x = 1 := (S.rho_eq_one_iff x).2 (Subgroup.mem_centralizer_iff.2
      fun v hv => by
        have := hall v hv
        calc v * x = (x : G) * v * (x : G)⁻¹ * x := by rw [this]
          _ = x * v := by group)
    rw [hx] at h1
    exact absurd h1 (by decide)
  have hxV : ∀ v ∈ V, (x : G) * v * (x : G)⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp x.2 v).mp hv
  set v : G := κ ⟨v₀, hVUL hv₀V⟩ with hvdef
  have hvA : v ∈ A := ⟨_, rfl⟩
  have hvV : v ∈ V := by
    show v₀ * x * v₀⁻¹ * (x : G)⁻¹ ∈ V
    have e : v₀ * x * v₀⁻¹ * (x : G)⁻¹ = v₀ * ((x : G) * v₀⁻¹ * (x : G)⁻¹) := by group
    rw [e]
    exact V.mul_mem hv₀V (hxV _ (V.inv_mem hv₀V))
  have hv1 : v ≠ 1 := by
    intro h
    apply hv₀
    have h' : v₀ * x * v₀⁻¹ * (x : G)⁻¹ = 1 := h
    calc (x : G) * v₀ * (x : G)⁻¹ = (x : G) * v₀ * (x : G)⁻¹ *
          (v₀ * x * v₀⁻¹ * (x : G)⁻¹) := by rw [h', mul_one]
      _ = v₀ := by
        have hc := hULab _ (hVUL hv₀V) _ (hxUL _ (UL.inv_mem (hVUL hv₀V)))
        calc (x : G) * v₀ * (x : G)⁻¹ * (v₀ * x * v₀⁻¹ * (x : G)⁻¹) =
            (x : G) * v₀ * (x : G)⁻¹ * (v₀ * ((x : G) * v₀⁻¹ * (x : G)⁻¹)) := by group
          _ = (x : G) * v₀ * (x : G)⁻¹ * (((x : G) * v₀⁻¹ * (x : G)⁻¹) * v₀) := by rw [hc]
          _ = v₀ := by group
  set kk : Fin 4 → Fin 15 := ![3, 7, 10, 12] with hkk
  have hu₁UL : u₁ ∈ UL := le_conjClosure _ L (S.U1c_le_UH hu₁)
  have huUL : ∀ i, (S.lk (kk i) : G) * u₁ * (S.lk (kk i) : G)⁻¹ ∈ UL := fun i =>
    mem_conjClosure (S.lk_mem (kk i)) (S.U1c_le_UH hu₁)
  let w : Fin 4 → G := fun i => κ ⟨_, huUL i⟩
  have hwA : ∀ i, w i ∈ A := fun i => ⟨_, rfl⟩
  obtain ⟨ε, hε, hεV⟩ := exists_prod4_mem (A := A) (V := V)
    (fun a ha b hb => hULab a (hAUL ha) b (hAUL hb)) (fun a ha => hULsq a (hAUL ha))
    hAcard hvA hvV hv1 hwA
  refine ⟨ε, hε, fun q hq => ?_⟩
  have hQC := S.pCoreOf_LT_le_centralizer hq
  have hcw : ∀ i, q * w i * q⁻¹ * (w i)⁻¹ ∈ V ∧ S.coordV (q * w i * q⁻¹ * (w i)⁻¹) =
      S.Fq u₁ q (kk i) • dA (kk i) + S.Fq u₁ q (![4, 8, 11, 13] i) • dA (![4, 8, 11, 13] i) := by
    intro i
    set l := S.lk (kk i) with hl
    set u := (l : G) * u₁ * (l : G)⁻¹ with hu
    set l' : ↥(Subgroup.normalizer (V : Set G)) := x * l * x⁻¹ with hl'
    have hlL : (l : G) ∈ L := S.lk_mem (kk i)
    have hl'L : (l' : G) ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_NL hxT) l).mp hlL
    have hl'act : act4f (S.frame.ρ l') e0123 = dVec (![4, 8, 11, 13] i) := by
      rw [hl', map_mul, map_mul, map_inv, hx, act4f_mul, act4f_mul, swap_inv,
        act4f_swap45_e0123, S.lk_act, act4f_dVec, dPerm_swap45]
    have hxu : (x : G) * u * (x : G)⁻¹ = (l' : G) * ((x : G) * u₁ * (x : G)⁻¹) * (l' : G)⁻¹ := by
      rw [hu, hl']; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    have hc1 := S.comm_conj_u1_mem_V hβk hβe hu₁ hq hlL
    have hc2 := S.comm_conj_u1_mem_V hβk hβe hu₁ hq hl'L
    have hc2' : q * ((x : G) * u * (x : G)⁻¹) * q⁻¹ * ((x : G) * u * (x : G)⁻¹)⁻¹ =
        q * ((l' : G) * u₁ * (l' : G)⁻¹) * q⁻¹ * ((l' : G) * u₁ * (l' : G)⁻¹)⁻¹ := by
      rw [hxu]
      rcases S.conj_u1_eq hβk hβe hu₁ hu₁V hxG with h | h
      · rw [h]
      · rw [h]
        have e2 : (l' : G) * (u₁ * S.z) * (l' : G)⁻¹ =
            ((l' : G) * u₁ * (l' : G)⁻¹) * ((l' : G) * S.z * (l' : G)⁻¹) := by group
        rw [e2, comm_mul_mem_V hQC ((Subgroup.mem_normalizer_iff.mp l'.2 S.z).mp S.z_mem_V)]
    have hwi : w i = u * ((x : G) * u * (x : G)⁻¹)⁻¹ := by
      show u * x * u⁻¹ * (x : G)⁻¹ = _
      group
    have huU : u ∈ UL := huUL i
    have hxuU : (x : G) * u * (x : G)⁻¹ ∈ UL := hxUL _ huU
    have hV2 : q * ((x : G) * u * (x : G)⁻¹) * q⁻¹ * ((x : G) * u * (x : G)⁻¹)⁻¹ ∈ V := by
      rw [hc2']; exact hc2
    have hinv := comm_inv_of_comm (q := q) (hULab _ hxuU _ (hVUL hV2))
    have hV2' : q * ((x : G) * u * (x : G)⁻¹)⁻¹ * q⁻¹ * ((x : G) * u * (x : G)⁻¹)⁻¹⁻¹ ∈ V := by
      rw [hinv]; exact V.inv_mem hV2
    have hmul := comm_mul_of_comm (q := q) (a := u) (b := ((x : G) * u * (x : G)⁻¹)⁻¹)
      (hULab _ huU _ (hVUL hV2'))
    rw [hwi, hmul]
    refine ⟨V.mul_mem hc1 hV2', ?_⟩
    rw [S.coordV_mul hc1 hV2', hinv]
    have hinvV : ∀ y ∈ V, y⁻¹ = y := fun y hy => by
      have := S.elemAbelian_V.2 y hy
      rw [sq] at this
      exact inv_eq_of_mul_eq_one_left this
    rw [hinvV _ hV2, hc2', S.coordV_of_mem hc1, S.coordV_of_mem hc2,
      S.psi_comm_eq hβk hβe hu₁ hu₁V hq hlL (S.lk_act (kk i)) hc1,
      S.psi_comm_eq hβk hβe hu₁ hu₁V hq hl'L hl'act hc2]
  have hW : q * prod4 w ε * q⁻¹ * (prod4 w ε)⁻¹ = 1 := by
    have hc := Subgroup.mem_centralizer_iff.mp hQC _ hεV
    rw [← hc]; group
  rw [comm_prod4 (U := UL) hULab (fun i => hAUL (hwA i)) (fun i => hVUL (hcw i).1)] at hW
  have h0 := congrArg S.coordV hW
  rw [S.coordV_prod4 (fun i => (hcw i).1), S.coordV_one] at h0
  rw [ConI_rEps_iff]
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hcw i).2]

end Rel

end Setting4

end CFSG.Quasithin.H13.A6
