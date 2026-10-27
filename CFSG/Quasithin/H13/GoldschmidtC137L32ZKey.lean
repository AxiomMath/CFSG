module

public import CFSG.Quasithin.H13.GoldschmidtC137Cocycle
public import CFSG.Quasithin.H13.GoldschmidtC137L32Coord
public import CFSG.Quasithin.H13.GoldschmidtC137L3Pair
public import CFSG.Quasithin.H13.GoldschmidtC137L3Fin
public import CFSG.Quasithin.Background.B4L3Key

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.L3 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem exists_pow_eq_one_of_sq_mem_pCore {L : Subgroup G} (l : ↥L)
    (h : l * l ∈ CFSG.pCore 2 ↥L) : ∃ n : ℕ, (l : G) ^ (2 ^ n) = 1 := by
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨l * l, h⟩
  refine ⟨n + 1, ?_⟩
  have h1 : (l * l) ^ (2 ^ n) = 1 := by
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => (y : ↥L)) hn
    simpa using this
  have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
  have h2 : l ^ (2 ^ (n + 1)) = 1 := by
    rw [h3, pow_mul, sq]
    exact h1
  have := congrArg (fun y : ↥L => (y : G)) h2
  simpa using this

theorem zcentral_of_sum [Finite G] {L M K P' : Subgroup G} {u z : G} {F : Type} [Field F]
    [Fintype F] (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168)
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hM : IsSumOfNaturalModulesVia L M ⊥ α false j) (huM : u ∈ M) (hu1 : u ≠ 1)
    (hKL : K ≤ L) (hKu : ∀ l ∈ L, l * u = u * l → l ∈ K) (hKu' : ∀ k ∈ K, k * u = u * k)
    (hP' : IsSylowTwoOf P' K) (hzP' : ∀ p ∈ P', p * z = z * p)
    (hc : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ M) : ∀ k ∈ K, k * z = z * k := by
  obtain ⟨α'', β', hsurj, hker, hLM, hβ⟩ := exists_coords hcard hα hM
  have hMc : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    intro a ha b hb
    have h1 : β' (⟨a, ha⟩ * ⟨b, hb⟩ : ↥M) = β' (⟨b, hb⟩ * ⟨a, ha⟩ : ↥M) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (β'.injective h1)
  have hM2 : ∀ a ∈ M, a * a = 1 := by
    intro a ha
    have h1 : β' (⟨a, ha⟩ * ⟨a, ha⟩ : ↥M) = β' 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      funext i
      funext p
      simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
      have := vec_add_self (Multiplicative.toAdd (β' ⟨a, ha⟩) i)
      exact congrFun this p
    exact congrArg Subtype.val (β'.injective h1)
  set e : Fin j → Vec := fun i => Multiplicative.toAdd (β' ⟨u, huM⟩) i with he
  have he0 : e ≠ 0 := by
    intro h0
    apply hu1
    have : β' ⟨u, huM⟩ = β' 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      funext i
      exact congrFun h0 i
    exact congrArg Subtype.val (β'.injective this)
  have hLfix : ∀ (l : ↥L) (m : G) (hm : m ∈ M), (l : G) * m = m * l ↔
      ∀ i, act (α'' l) (Multiplicative.toAdd (β' ⟨m, hm⟩) i) =
        Multiplicative.toAdd (β' ⟨m, hm⟩) i := by
    intro l m hm
    have hlN : (l : G) ∈ normalizer (M : Set G) := hLM l.2
    constructor
    · intro hl i
      have hv : ((⟨m, hm⟩ : ↥M) : G) = (l : G) * ((⟨m, hm⟩ : ↥M) : G) * (l : G)⁻¹ := by
        show m = (l : G) * m * (l : G)⁻¹
        rw [hl]
        group
      exact (hβ l ⟨m, hm⟩ ⟨m, hm⟩ hv i).symm
    · intro h
      have hmem : (l : G) * m * (l : G)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hlN m).1 hm
      have hv : ((⟨(l : G) * m * (l : G)⁻¹, hmem⟩ : ↥M) : G) =
          (l : G) * ((⟨m, hm⟩ : ↥M) : G) * (l : G)⁻¹ := rfl
      have h1 : β' ⟨(l : G) * m * (l : G)⁻¹, hmem⟩ = β' ⟨m, hm⟩ := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [hβ l ⟨m, hm⟩ _ hv i]
        exact h i
      have h2 := congrArg Subtype.val (β'.injective h1)
      have h3 : (l : G) * m * (l : G)⁻¹ = m := h2
      calc (l : G) * m = ((l : G) * m * (l : G)⁻¹) * l := by group
        _ = m * l := by rw [h3]
  have hKfix : ∀ (k : G) (hk : k ∈ K), ∀ i, act (α'' ⟨k, hKL hk⟩) (e i) = e i := by
    intro k hk i
    exact (hLfix ⟨k, hKL hk⟩ u huM).1 (hKu' k hk) i
  have hcls : (∃ e₀ : Vec, e₀ ≠ 0 ∧ ∀ i, e i = 0 ∨ e i = e₀) ∨
      (∀ g : Γ, (∀ i, act g (e i) = e i) → g * g = 1) := by
    rcases hj with rfl | rfl
    · left
      have : e 0 ≠ 0 := fun h0 => he0 (funext fun i => by
        rw [Fin.fin_one_eq_zero i]; exact h0)
      exact ⟨e 0, this, fun i => Or.inr (by rw [Fin.fin_one_eq_zero i])⟩
    · rcases stab_pair_cases (e 0) (e 1) (by
        by_contra hh
        push Not at hh
        exact he0 (funext fun i => by fin_cases i <;> simp [hh.1, hh.2])) with h | h
      · obtain ⟨e₀, he₀, h1, h2⟩ := h
        left
        exact ⟨e₀, he₀, fun i => by fin_cases i <;> simpa using ‹_›⟩
      · right
        intro g hg
        exact h g (hg 0) (hg 1)
  rcases hcls with ⟨e₀, he₀, hee⟩ | hb
  ·
    have hstab : ∀ (k : G) (hk : k ∈ K), act (α'' ⟨k, hKL hk⟩) e₀ = e₀ := by
      intro k hk
      obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
        by_contra hh
        push Not at hh
        exact he0 (funext hh)
      rcases hee i with h0 | h0
      · exact absurd h0 hi
      · rw [← h0]
        exact hKfix k hk i
    let N₀ : Subgroup G := (Subgroup.comap α'' (v4Γ e₀ he₀)).map L.subtype
    have hN₀ : ∀ x : G, x ∈ N₀ ↔ ∃ l : ↥L, α'' l ∈ v4Γ e₀ he₀ ∧ (l : G) = x := fun x => by
      rw [Subgroup.mem_map]
      exact ⟨fun ⟨l, hl, hlx⟩ => ⟨l, Subgroup.mem_comap.1 hl, hlx⟩,
        fun ⟨l, hl, hlx⟩ => ⟨l, Subgroup.mem_comap.2 hl, hlx⟩⟩
    have hN₀K : N₀ ≤ K := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := (hN₀ x).1 hx
      apply hKu _ l.2
      refine (hLfix l u huM).2 fun i => ?_
      rcases hee i with h0 | h0
      · show act (α'' l) (e i) = e i
        rw [h0, act_zero]
      · show act (α'' l) (e i) = e i
        rw [h0]
        exact v4_stab e₀ he₀ _ (mem_v4Γ.1 hl)
    have hN₀norm : K ≤ normalizer (N₀ : Set G) := by
      have key : ∀ k ∈ K, ∀ x ∈ N₀, k * x * k⁻¹ ∈ N₀ := by
        intro k hk x hx
        obtain ⟨l, hl, rfl⟩ := (hN₀ x).1 hx
        refine (hN₀ _).2 ⟨⟨k, hKL hk⟩ * l * ⟨k, hKL hk⟩⁻¹, ?_, rfl⟩
        rw [map_mul, map_mul, map_inv]
        exact v4Γ_normal e₀ he₀ _ (hstab k hk) _ hl
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key k hk x, fun h => ?_⟩
      have := key k⁻¹ (K.inv_mem hk) _ h
      simpa [mul_assoc] using this
    have hN₀2 : IsPGroup 2 N₀ := by
      rintro ⟨x, hx⟩
      obtain ⟨l, hl, rfl⟩ := (hN₀ x).1 hx
      have h1 : l * l ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, MonoidHom.mem_ker, map_mul]
        exact (AS_elem e₀ he₀ _ (mem_v4Γ.1 hl) _ (mem_v4Γ.1 hl)).2
      obtain ⟨n, hn⟩ := exists_pow_eq_one_of_sq_mem_pCore l h1
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    have hP'N₀ : N₀ ≤ P' :=
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN₀K hN₀norm hN₀2).trans
        (pCoreOf_two_le_of_sylowIn hP'.1 hP'.2.1 hP'.2.2)
    have hfix : ∀ m ∈ M, (∀ p ∈ P', p * m * p⁻¹ = m) → ∀ k ∈ K, k * m * k⁻¹ = m := by
      intro m hm hPm k hk
      have hcoord : ∀ i, Multiplicative.toAdd (β' ⟨m, hm⟩) i = 0 ∨
          Multiplicative.toAdd (β' ⟨m, hm⟩) i = e₀ := by
        intro i
        apply v4_fix e₀ he₀
        intro g hg
        obtain ⟨l, hl⟩ := hsurj g
        have hlN : (l : G) ∈ N₀ := (hN₀ _).2 ⟨l, mem_v4Γ.2 (by rw [hl]; exact hg), rfl⟩
        have hcomm : (l : G) * m = m * l := by
          have := hPm l (hP'N₀ hlN)
          calc (l : G) * m = ((l : G) * m * (l : G)⁻¹) * l := by group
            _ = m * l := by rw [this]
        rw [← hl]
        exact (hLfix l m hm).1 hcomm i
      have h1 : k * m = m * k := (hLfix ⟨k, hKL hk⟩ m hm).2 fun i => by
        rcases hcoord i with h0 | h0
        · rw [h0, act_zero]
        · rw [h0]
          exact hstab k hk
      calc k * m * k⁻¹ = (m * k) * k⁻¹ := by rw [h1]
        _ = m := by group
    exact commutes_of_cocycle hP'.1 (hKL.trans hLM) hMc hM2 hP'.2.2 hc hzP' hfix
  ·
    have hK2 : IsPGroup 2 ↥K := by
      intro x
      have hl : (⟨x, hKL x.2⟩ : ↥L) * ⟨x, hKL x.2⟩ ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, MonoidHom.mem_ker, map_mul]
        exact hb _ (hKfix x x.2)
      obtain ⟨n, hn⟩ := exists_pow_eq_one_of_sq_mem_pCore _ hl
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    have hPK : P' = K := CFSG.Quasithin.F1.eq_of_isSylowTwoOf_le hP' le_rfl hK2 hP'.1
    intro k hk
    exact hzP' k (hPK ▸ hk)

end CFSG.Quasithin.H13.U3.GC137
