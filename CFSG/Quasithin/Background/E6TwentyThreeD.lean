module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.C2Six
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block

public section

namespace CFSG.Quasithin.E6.A3Push

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_eq_of_mul_inv_mem {N : Subgroup G} {x b : G} (hx3 : x ^ 3 = 1)
    (hN2 : IsPGroup 2 N) (hxN : ∀ n ∈ N, x * n * x⁻¹ = n) (hb : x * b * x⁻¹ * b⁻¹ ∈ N) :
    x * b * x⁻¹ = b := by
  have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
  obtain ⟨r, hr⟩ : ∃ r, r = x * b * x⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hr] at hb
  have h1 : x * b * x⁻¹ = r * b := by rw [hr]; group
  have hxr := hxN r hb
  have h2 : x * (x * b * x⁻¹) * x⁻¹ = r * r * b := by
    rw [h1, show x * (r * b) * x⁻¹ = (x * r * x⁻¹) * (x * b * x⁻¹) by group, hxr, h1, mul_assoc]
  have h3 : x * (x * (x * b * x⁻¹) * x⁻¹) * x⁻¹ = r * r * r * b := by
    rw [h2, show x * (r * r * b) * x⁻¹ = (x * r * x⁻¹) * (x * r * x⁻¹) * (x * b * x⁻¹) by group,
      hxr, h1]
    group
  have h4 : x * (x * (x * b * x⁻¹) * x⁻¹) * x⁻¹ = b := by
    calc x * (x * (x * b * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * b * (x * x * x)⁻¹ := by group
      _ = b := by rw [hx3']; group
  have hr3 : r * r * r = 1 := by
    have : r * r * r * b = b := h3.symm.trans h4
    simpa using this
  have hr1 : r = 1 := by
    have hr3' : r ^ 3 = 1 := by rw [pow_three, ← mul_assoc, hr3]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hN2) ⟨r, hb⟩
    have hdvd : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3'
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at hdvd
    have : 2 ^ k = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exfalso
        rcases k with _ | k
        · simp at h
        · have : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
          rw [h] at this
          omega
    rw [this] at hk
    exact orderOf_eq_one_iff.mp hk
  rw [h1, hr1, one_mul]

theorem mem_of_cocycle {B A N : Subgroup G}
    (hB1 : ∀ (K : Subgroup ↥B) [K.Normal], IsPGroup 2 (↥B ⧸ K) → K = ⊤)
    (hA2 : IsPGroup 2 A) (hNA : N ≤ A) (hNn : (N.subgroupOf A).Normal)
    (hact : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ N)
    (f : G → G) (hfA : ∀ b ∈ B, f b ∈ A)
    (hf : ∀ b ∈ B, ∀ c ∈ B, f (b * c) = f b * (b * f c * b⁻¹)) :
    ∀ b ∈ B, f b ∈ N := by
  have hconjA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := fun b hb a ha => by
    have := A.mul_mem (hNA (hact b hb a ha)) ha
    simpa using this
  have hf1 : f 1 = 1 := by
    have h := hf 1 B.one_mem 1 B.one_mem
    simp only [one_mul, inv_one, mul_one] at h
    have := congrArg (fun y => (f 1)⁻¹ * y) h
    simpa using this.symm
  let ψ : ↥B →* ↥A ⧸ N.subgroupOf A :=
    { toFun := fun b => QuotientGroup.mk (⟨f b, hfA b b.2⟩ : ↥A)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf]
        simp only [OneMemClass.coe_one, hf1]
        exact N.one_mem
      map_mul' := fun b c => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hf b b.2 c c.2]
        obtain ⟨bg, hbg⟩ : ∃ g : G, g = (b : G) := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ : ∃ g : G, g = f (c : G) := ⟨_, rfl⟩
        have hyA : y ∈ A := hy ▸ hfA c c.2
        rw [← hbg, ← hy]
        have h := hact bg (hbg ▸ b.2) y hyA
        have hi : (bg * y * bg⁻¹ * y⁻¹)⁻¹ ∈ N := N.inv_mem h
        have e : (f bg * (bg * y * bg⁻¹))⁻¹ * (f bg * y) =
            y⁻¹ * (bg * y * bg⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by
          group
        rw [e]
        have := hNn.conj_mem ⟨(bg * y * bg⁻¹ * y⁻¹)⁻¹, hNA hi⟩ (Subgroup.mem_subgroupOf.mpr hi)
          ⟨y⁻¹, A.inv_mem hyA⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this }
  have hψ : ∀ b : ↥B, ψ b = QuotientGroup.mk (⟨f b, hfA b b.2⟩ : ↥A) := fun _ => rfl
  have hq : IsPGroup 2 (↥B ⧸ ψ.ker) := by
    have hinj := QuotientGroup.kerLift_injective ψ
    have hP : IsPGroup 2 (↥A ⧸ N.subgroupOf A) := hA2.to_quotient _
    exact hP.of_injective _ hinj
  have hker := hB1 ψ.ker hq
  intro b hb
  have hmem : (⟨b, hb⟩ : ↥B) ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmem
  exact hmem


theorem exists_pow_mul_inv_mem_of_alt3 {B : Subgroup G} (hB3 : IsAltType B 3) {c : G}
    (hcB : c ∈ B) (hcQ : c ∉ blockQ B) {b : G} (hb : b ∈ B) :
    ∃ k : ℕ, k < 3 ∧ b * (c ^ k)⁻¹ ∈ blockQ B := by
  classical
  obtain ⟨α, hαs, hαk, -⟩ := hB3
  set g := α ⟨c, hcB⟩ with hg
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hg1 : g ≠ 1 := by
    intro h
    apply hcQ
    have : (⟨c, hcB⟩ : ↥B) ∈ α.ker := h
    rw [hαk] at this
    exact CFSG.Quasithin.C2Six.mem_pCore_two_iff.mp this
  have hog : orderOf g = 3 := by
    have hdvd : orderOf g ∣ 3 := by
      have := orderOf_dvd_natCard g
      rwa [hcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hog, hcard]
  have hmem : α ⟨b, hb⟩ ∈ Subgroup.zpowers g := by rw [htop]; exact Subgroup.mem_top _
  rw [mem_zpowers_iff_mem_range_orderOf, hog, Finset.mem_image] at hmem
  obtain ⟨k, hk, hkb⟩ := hmem
  refine ⟨k, Finset.mem_range.mp hk, ?_⟩
  have hker : (⟨b, hb⟩ : ↥B) * (⟨c, hcB⟩ ^ k)⁻¹ ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, ← hg, hkb, mul_inv_cancel]
  rw [hαk] at hker
  have := CFSG.Quasithin.C2Six.mem_pCore_two_iff.mp hker
  simpa [blockQ] using this

variable [Finite G]

theorem centralizes_blockU {B : Subgroup G} {x : G} (hB : IsShort2 B)
    (hB' : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ blockQ B)
    (hU' : ∀ u ∈ blockU B, x * u * x⁻¹ * u⁻¹ ∈ blockZ B) :
    ∀ u ∈ blockU B, x * u * x⁻¹ = u := by
  have hUab : ∀ u ∈ blockU B, ∀ v ∈ blockU B, u * v = v * u := fun u hu v hv =>
    C1.blockU_comm hB u hu v (C1.blockU_le_blockQ hB hv)
  have hsub : blockU B ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← C1.commutator_blockU hB, Subgroup.commutator_le]
    intro u hu b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ blockZ B, x * u * x⁻¹ = z * u :=
      ⟨_, hU' u hu, by group⟩
    obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ blockQ B, x * b * x⁻¹ = q * b :=
      ⟨_, hB' b hb, by group⟩
    have hzU : z ∈ blockU B := hzZ.1
    have hzb : b * z⁻¹ * b⁻¹ = z⁻¹ := by
      have := (Subgroup.mem_centralizer_iff.mp hzZ.2) b hb
      calc b * z⁻¹ * b⁻¹ = z⁻¹ * (z * b) * z⁻¹ * b⁻¹ := by group
        _ = z⁻¹ * (b * z) * z⁻¹ * b⁻¹ := by rw [this]
        _ = z⁻¹ := by group
    set w := b * u⁻¹ * b⁻¹ with hw
    have hwU : w ∈ blockU B :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hb) u⁻¹).mp (inv_mem hu)
    have hwz : w * z⁻¹ ∈ blockU B := mul_mem hwU (inv_mem hzU)
    have hq' : q * (w * z⁻¹) * q⁻¹ = w * z⁻¹ := by
      rw [← C1.blockU_comm hB _ hwz q hqQ]
      group
    have key : x * ⁅u, b⁆ * x⁻¹ = ⁅u, b⁆ := by
      calc x * ⁅u, b⁆ * x⁻¹
          = (x * u * x⁻¹) * (x * b * x⁻¹) * (x * u * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = z * u * (q * (w * (b * z⁻¹ * b⁻¹)) * q⁻¹) := by rw [hz, hq, hw]; group
        _ = z * u * (w * z⁻¹) := by rw [hzb, hq']
        _ = u * w := by
            rw [show z * u * (w * z⁻¹) = (z * (u * w)) * z⁻¹ by group,
              hUab z hzU (u * w) (mul_mem hu hwU)]
            group
        _ = ⁅u, b⁆ := by rw [hw, commutatorElement_def]; group
    calc ⁅u, b⁆ * x = (x * ⁅u, b⁆ * x⁻¹) * x := by rw [key]
      _ = x * ⁅u, b⁆ := by group
  intro u hu
  have := Subgroup.mem_centralizer_singleton_iff.mp (hsub hu)
  rw [← this]
  group

theorem centralizes_of_trivial {B : Subgroup G} {x : G} (hB : IsShort2 B) (hx3 : x ^ 3 = 1)
    (hB' : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ blockQ B)
    (hU' : ∀ u ∈ blockU B, x * u * x⁻¹ * u⁻¹ ∈ blockZ B) :
    ∀ b ∈ B, x * b * x⁻¹ = b := by
  have hxU := centralizes_blockU hB hB' hU'
  have hQ2 : IsPGroup 2 (blockQ B) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
  have hmem : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ blockU B := by
    refine mem_of_cocycle hB.1 hQ2 (C1.blockU_le_blockQ hB) ?_ ?_
      (fun b => x * b * x⁻¹ * b⁻¹) hB' ?_
    · constructor
      intro n hn a
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have haB : (a : G) ∈ B := (CFSG.LieType.BorelTits.pCoreOf_le 2 B) a.2
      exact (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B haB) n).mp hn
    · intro b hb a ha
      exact C1.commutator_mem_blockU' hb ha
    · intro b _ c _
      group
  intro b hb
  exact conj_eq_of_mul_inv_mem hx3 (C1.isPGroup_blockU hB) hxU (hmem b hb)


theorem mul_inv_mem_blockZ_of_card {B E : Subgroup G} {x : G} (hB : IsShort2 B)
    (hxB : x ∈ Subgroup.normalizer (B : Set G))
    (hB' : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ blockQ B)
    (hE : ∀ u ∈ blockU B, x * u * x⁻¹ * u⁻¹ ∈ E) (hE4 : Nat.card E ≤ 4)
    (h16 : 16 * Nat.card (blockZ B) ≤ Nat.card (blockU B)) :
    ∀ u ∈ blockU B, x * u * x⁻¹ * u⁻¹ ∈ blockZ B := by
  classical
  have hUab : ∀ u ∈ blockU B, ∀ v ∈ blockU B, u * v = v * u := fun u hu v hv =>
    C1.blockU_comm hB u hu v (C1.blockU_le_blockQ hB hv)
  have hxU : x ∈ Subgroup.normalizer (blockU B : Set G) := C1.mem_normalizer_blockU hxB
  have hxZ : x ∈ Subgroup.normalizer (blockZ B : Set G) := C1.mem_normalizer_blockZ hxB
  have hcU : ∀ u ∈ blockU B, x * u * x⁻¹ ∈ blockU B := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hxU u).mp hu
  have hdU : ∀ u ∈ blockU B, x * u * x⁻¹ * u⁻¹ ∈ blockU B := fun u hu =>
    mul_mem (hcU u hu) (inv_mem hu)
  let d : ↥(blockU B) →* ↥(blockU B) :=
    { toFun := fun u => ⟨x * u * x⁻¹ * u⁻¹, hdU u u.2⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by
        obtain ⟨u, hu⟩ := u
        obtain ⟨v, hv⟩ := v
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have h1 := hUab _ (hcU v hv) _ (inv_mem hu)
        have h2 := hUab _ (inv_mem hv) _ (inv_mem hu)
        calc x * (u * v) * x⁻¹ * (u * v)⁻¹
            = (x * u * x⁻¹) * ((x * v * x⁻¹) * (v⁻¹ * u⁻¹)) := by group
          _ = (x * u * x⁻¹) * ((x * v * x⁻¹) * (u⁻¹ * v⁻¹)) := by rw [h2]
          _ = (x * u * x⁻¹) * (((x * v * x⁻¹) * u⁻¹) * v⁻¹) := by group
          _ = (x * u * x⁻¹) * ((u⁻¹ * (x * v * x⁻¹)) * v⁻¹) := by rw [h1]
          _ = x * u * x⁻¹ * u⁻¹ * (x * v * x⁻¹ * v⁻¹) := by group }
  have hd : ∀ u : ↥(blockU B), ((d u : ↥(blockU B)) : G) = x * u * x⁻¹ * (u : G)⁻¹ :=
    fun _ => rfl
  let W : Subgroup G := ((blockZ B).subgroupOf (blockU B)).comap d |>.map (blockU B).subtype
  have hmemW : ∀ u : G, u ∈ W ↔ u ∈ blockU B ∧ x * u * x⁻¹ * u⁻¹ ∈ blockZ B := by
    intro u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, by simpa [Subgroup.mem_subgroupOf, hd] using hv⟩
    · rintro ⟨hu, hz⟩
      exact ⟨⟨u, hu⟩, by simpa [Subgroup.mem_subgroupOf, hd] using hz, rfl⟩
  have hZW : blockZ B ≤ W := by
    intro z hz
    refine (hmemW z).mpr ⟨hz.1, ?_⟩
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hxZ z).mp hz) (inv_mem hz)
  have hWU : W ≤ blockU B := fun u hu => ((hmemW u).mp hu).1
  have hZB : ∀ b ∈ B, ∀ z ∈ blockZ B, b * z * b⁻¹ = z := fun b hb z hz => by
    have := (Subgroup.mem_centralizer_iff.mp hz.2) b hb
    rw [this]
    group
  have fwd : ∀ b ∈ B, ∀ u ∈ W, b * u * b⁻¹ ∈ W := by
    intro b hb u hu
    obtain ⟨huU, hz⟩ := (hmemW u).mp hu
    obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ blockQ B, x * b * x⁻¹ = q * b := ⟨_, hB' b hb, by group⟩
    have hbu : b * (x * u * x⁻¹) * b⁻¹ ∈ blockU B :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hb) _).mp (hcU u huU)
    have hq1 : q * (b * (x * u * x⁻¹) * b⁻¹) * q⁻¹ = b * (x * u * x⁻¹) * b⁻¹ := by
      rw [← C1.blockU_comm hB _ hbu q hqQ]
      group
    have key : x * (b * u * b⁻¹) * x⁻¹ * (b * u * b⁻¹)⁻¹ = b * (x * u * x⁻¹ * u⁻¹) * b⁻¹ := by
      calc x * (b * u * b⁻¹) * x⁻¹ * (b * u * b⁻¹)⁻¹
          = (x * b * x⁻¹) * (x * u * x⁻¹) * (x * b * x⁻¹)⁻¹ * (b * u * b⁻¹)⁻¹ := by group
        _ = q * (b * (x * u * x⁻¹) * b⁻¹) * q⁻¹ * (b * u * b⁻¹)⁻¹ := by rw [hq]; group
        _ = b * (x * u * x⁻¹) * b⁻¹ * (b * u * b⁻¹)⁻¹ := by rw [hq1]
        _ = b * (x * u * x⁻¹ * u⁻¹) * b⁻¹ := by group
    refine (hmemW _).mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hb) u).mp huU, ?_⟩
    rw [key, hZB b hb _ hz]
    exact hz
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fwd b hb u, fun h => ?_⟩
    have := fwd b⁻¹ (inv_mem hb) _ h
    simpa [mul_assoc] using this
  rcases hB.2.2.2.2.2 W hZW hWU hBW with hW | hW
  ·
    exfalso
    have hker : d.ker ≤ (blockZ B).subgroupOf (blockU B) := by
      intro u hu
      have h1 : (u : G) ∈ W := (hmemW u).mpr ⟨u.2, by
        have : ((d u : ↥(blockU B)) : G) = 1 := by rw [MonoidHom.mem_ker.mp hu]; rfl
        rw [← hd, this]
        exact one_mem _⟩
      rw [hW] at h1
      exact Subgroup.mem_subgroupOf.mpr h1
    have h1 : Nat.card (blockU B) = Nat.card d.range * Nat.card d.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange d).toEquiv,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have h2 : Nat.card d.ker ≤ Nat.card (blockZ B) := by
      calc Nat.card d.ker ≤ Nat.card ((blockZ B).subgroupOf (blockU B)) :=
            Subgroup.card_le_of_le hker
        _ = Nat.card (blockZ B) := Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ B ≤ blockU B)).toEquiv
    have h3 : Nat.card d.range ≤ Nat.card E := by
      have hmemE : ∀ w : ↥d.range, ((w : ↥(blockU B)) : G) ∈ E := by
        rintro ⟨w, u, rfl⟩
        rw [hd]
        exact hE u u.2
      refine Nat.card_le_card_of_injective (fun w : ↥d.range => (⟨_, hmemE w⟩ : ↥E)) ?_
      intro w₁ w₂ h
      have h' := congrArg (fun e : ↥E => (e : G)) h
      exact Subtype.ext (Subtype.ext h')
    have h4 : 0 < Nat.card (blockZ B) := Nat.card_pos
    have : Nat.card (blockU B) ≤ 4 * Nat.card (blockZ B) := by
      rw [h1]
      exact Nat.mul_le_mul (h3.trans hE4) h2
    omega
  · intro u hu
    have : u ∈ W := by rw [hW]; exact hu
    exact ((hmemW u).mp this).2

theorem centralizes_of_centralizes_blockQ {B : Subgroup G} {x : G} (hB : IsShort2 B)
    (hx3 : x ^ 3 = 1) (hxB : x ∈ Subgroup.normalizer (B : Set G))
    (hxQ : ∀ q ∈ blockQ B, x * q * x⁻¹ = q) : ∀ b ∈ B, x * b * x⁻¹ = b := by
  have hQ2 : IsPGroup 2 (blockQ B) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
  intro b hb
  have hxb : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hxB b).mp hb
  have hr : b⁻¹ * (x * b * x⁻¹) ∈ blockQ B := by
    refine hB.2.1 (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb) hxb, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hbq : b * q * b⁻¹ ∈ blockQ B :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ B hb) q).mp hq
    have h1 := hxQ q hq
    have h2 := hxQ _ hbq
    have h1' : x⁻¹ * q * x = q := by
      calc x⁻¹ * q * x = x⁻¹ * (x * q * x⁻¹) * x := by rw [h1]
        _ = q := by group
    have hrq : b⁻¹ * (x * b * x⁻¹) * q * (b⁻¹ * (x * b * x⁻¹))⁻¹ = q := by
      calc b⁻¹ * (x * b * x⁻¹) * q * (b⁻¹ * (x * b * x⁻¹))⁻¹
          = b⁻¹ * x * b * (x⁻¹ * q * x) * b⁻¹ * x⁻¹ * b := by group
        _ = b⁻¹ * (x * (b * q * b⁻¹) * x⁻¹) * b := by rw [h1']; group
        _ = q := by rw [h2]; group
    calc q * (b⁻¹ * (x * b * x⁻¹))
        = (b⁻¹ * (x * b * x⁻¹) * q * (b⁻¹ * (x * b * x⁻¹))⁻¹) * (b⁻¹ * (x * b * x⁻¹)) := by
          rw [hrq]
      _ = b⁻¹ * (x * b * x⁻¹) * q := by group
  have hmem : x * b * x⁻¹ * b⁻¹ ∈ blockQ B := by
    have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ B hb) _).mp hr
    simpa [mul_assoc] using this
  exact conj_eq_of_mul_inv_mem hx3 hQ2 hxQ hmem

theorem centralizes_blockQ_of_alt3 {B : Subgroup G} {a x : G} (hB : IsShort2 B)
    (hB3 : IsAltType B 3) (haB : a ∈ Subgroup.normalizer (B : Set G))
    (haQ : ∀ q ∈ blockQ B, a * q = q * a) (haC : ¬ ∀ b ∈ B, a * b = b * a)
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) (hx3 : x ^ 3 = 1) (hxa : x * a = a * x) :
    ∀ q ∈ blockQ B, x * q * x⁻¹ = q := by
  classical
  obtain ⟨hQU, hU4, hUsq, hUcomm, -, -, c, hcB, hc3, -, hfpf, hBeq⟩ := hB.alt3_structure hB3
  rw [← hQU] at hU4 hUsq hUcomm hfpf
  have hQ2 : IsPGroup 2 (blockQ B) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
  have hcQ : c ∉ blockQ B := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨c, h⟩
    rw [Subgroup.orderOf_mk, hc3] at hk
    have : (2 : ℕ) ∣ 3 := by
      rcases k with _ | k
      · simp at hk
      · rw [hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    omega
  have hxa' : x * a * x⁻¹ = a := by rw [hxa]; group
  have hconjB : ∀ {y : G}, y ∈ Subgroup.normalizer (B : Set G) → ∀ b ∈ B, y * b * y⁻¹ ∈ B :=
    fun hy b hb => (Subgroup.mem_normalizer_iff.mp hy b).mp hb
  obtain ⟨δ, hδ⟩ : ∃ δ : G → G, ∀ b, δ b = a * b * a⁻¹ * b⁻¹ := ⟨_, fun _ => rfl⟩
  have hδQ : ∀ b ∈ B, δ b ∈ blockQ B := by
    intro b hb
    rw [hδ]
    refine hB.2.1 (Subgroup.mem_inf.mpr ⟨mul_mem (hconjB haB b hb) (inv_mem hb), ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hbq : b⁻¹ * q * b ∈ blockQ B := by
      have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ B (inv_mem hb)) q).mp hq
      simpa using this
    have h1 : a⁻¹ * (b⁻¹ * q * b) * a = b⁻¹ * q * b := by
      calc a⁻¹ * (b⁻¹ * q * b) * a = a⁻¹ * ((b⁻¹ * q * b) * a) := by group
        _ = a⁻¹ * (a * (b⁻¹ * q * b)) := by rw [haQ _ hbq]
        _ = b⁻¹ * q * b := by group
    have h2 : a * q * a⁻¹ = q := by rw [haQ q hq]; group
    calc q * (a * b * a⁻¹ * b⁻¹) = q * (a * b * a⁻¹ * b⁻¹) := rfl
      _ = (a * b * (a⁻¹ * (b⁻¹ * q * b) * a) * b⁻¹ * a⁻¹) * (a * b * a⁻¹ * b⁻¹) := by
          rw [h1]
          calc q * (a * b * a⁻¹ * b⁻¹) = (a * q * a⁻¹) * (a * b * a⁻¹ * b⁻¹) := by rw [h2]
            _ = _ := by group
      _ = (a * b * a⁻¹ * b⁻¹) * q := by group
  have hau : ∀ u ∈ blockQ B, a * u * a⁻¹ = u := fun u hu => by rw [haQ u hu]; group
  have hδu : ∀ u ∈ blockQ B, ∀ b ∈ B, δ (u * b) = δ b := by
    intro u hu b hb
    have hm := hδQ b hb
    rw [hδ] at hm
    rw [hδ, hδ]
    calc a * (u * b) * a⁻¹ * (u * b)⁻¹ = (a * u * a⁻¹) * (a * b * a⁻¹ * b⁻¹) * u⁻¹ := by group
      _ = u * (a * b * a⁻¹ * b⁻¹) * u⁻¹ := by rw [hau u hu]
      _ = a * b * a⁻¹ * b⁻¹ := by rw [hUcomm u hu _ hm]; group
  obtain ⟨e0, he0⟩ : ∃ e, e = δ c := ⟨_, rfl⟩
  have he0Q : e0 ∈ blockQ B := he0 ▸ hδQ c hcB
  have hδc2 : δ (c ^ 2) = e0 * (c * e0 * c⁻¹) := by
    rw [he0, hδ, hδ, pow_two]
    group
  obtain ⟨f, hf⟩ : ∃ f, f = e0 * (c * e0 * c⁻¹) := ⟨_, rfl⟩
  rw [← hf] at hδc2
  have hδval : ∀ b ∈ B, δ b = 1 ∨ δ b = e0 ∨ δ b = f := by
    intro b hb
    obtain ⟨k, hk, hkb⟩ := exists_pow_mul_inv_mem_of_alt3 hB3 hcB hcQ hb
    have hbk : δ b = δ (c ^ k) := by
      have := hδu _ hkb (c ^ k) (pow_mem hcB k)
      rwa [show b * (c ^ k)⁻¹ * c ^ k = b by group] at this
    interval_cases k
    · left; rw [hbk, hδ]; group
    · right; left; rw [hbk, pow_one, he0]
    · right; right; rw [hbk, hδc2]
  have he01 : e0 ≠ 1 := by
    intro h
    apply haC
    have hac : a * c = c * a := by
      have h' : a * c * a⁻¹ * c⁻¹ = 1 := by rw [← h, he0, hδ]
      calc a * c = (a * c * a⁻¹ * c⁻¹) * c * a := by group
        _ = c * a := by rw [h']; group
    have hle : B ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [hBeq]
      refine sup_le ?_ ?_
      · intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hQU] at hu
        exact haQ u hu |>.symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hac.symm
    intro b hb
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
  have he0sq : e0 * e0 = 1 := by rw [← pow_two]; exact hUsq e0 he0Q
  have hce0 : c * e0 * c⁻¹ ≠ 1 := by
    intro h; apply he01
    calc e0 = c⁻¹ * (c * e0 * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hfe0 : f ≠ e0 := by
    intro h; apply hce0
    have h' : e0 * (c * e0 * c⁻¹) = e0 * 1 := by rw [mul_one, ← hf, h]
    exact mul_left_cancel h'
  have hf1 : f ≠ 1 := by
    intro h; apply hfpf e0 he0Q he01
    have h2 : c * e0 * c⁻¹ = e0⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← hf, h])
    rw [h2]
    exact inv_eq_of_mul_eq_one_right he0sq
  have hxδ : ∀ b, x * δ b * x⁻¹ = δ (x * b * x⁻¹) := by
    intro b
    rw [hδ, hδ]
    calc x * (a * b * a⁻¹ * b⁻¹) * x⁻¹
        = (x * a * x⁻¹) * (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by group
      _ = _ := by rw [hxa']
  have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
  have hcube : ∀ y : G, x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = y := fun y => by
    calc x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * y * (x * x * x)⁻¹ := by group
      _ = y := by rw [hx3']; group
  have hxe0 : x * e0 * x⁻¹ = e0 := by
    have hval := hδval _ (hconjB hxB c hcB)
    rw [← hxδ, ← he0] at hval
    rcases hval with h | h | h
    · exfalso; apply he01
      calc e0 = x⁻¹ * (x * e0 * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact h
    · exfalso
      have hval2 := hδval _ (hconjB hxB (c ^ 2) (pow_mem hcB 2))
      rw [← hxδ, hδc2] at hval2
      rcases hval2 with h2 | h2 | h2
      · apply hf1
        calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
          _ = 1 := by rw [h2]; group
      · apply hfe0
        have := hcube e0
        rw [h, h2, h] at this
        exact this
      · apply hfe0
        calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
          _ = x⁻¹ * (x * e0 * x⁻¹) * x := by rw [h2, h]
          _ = e0 := by group
  have hxe0' : x⁻¹ * e0 * x = e0 := by
    calc x⁻¹ * e0 * x = x⁻¹ * (x * e0 * x⁻¹) * x := by rw [hxe0]
      _ = e0 := by group
  have hoe0 : orderOf e0 = 2 := orderOf_eq_prime (by rw [pow_two]; exact he0sq) he01
  have hzQ : Subgroup.zpowers e0 ≤ blockQ B := Subgroup.zpowers_le.mpr he0Q
  have hmemz : ∀ y : G, y ∈ Subgroup.zpowers e0 ↔ y = 1 ∨ y = e0 := by
    intro y
    rw [mem_zpowers_iff_mem_range_orderOf, hoe0, Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := Finset.mem_range.mp hk
      interval_cases k
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨1, by simp, by simp⟩
  have hidx : ((Subgroup.zpowers e0).subgroupOf (blockQ B)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers e0).subgroupOf (blockQ B))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzQ).toEquiv, Nat.card_zpowers, hoe0,
      hU4] at h1
    omega
  intro q hq
  have hxq : x * q * x⁻¹ ∈ blockQ B :=
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockQ hxB) q).mp hq
  have hiff : x * q * x⁻¹ ∈ Subgroup.zpowers e0 ↔ q ∈ Subgroup.zpowers e0 := by
    rw [hmemz, hmemz]
    constructor
    · rintro (h | h)
      · left; calc q = x⁻¹ * (x * q * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      · right; calc q = x⁻¹ * (x * q * x⁻¹) * x := by group
          _ = e0 := by rw [h, hxe0']
    · rintro (h | h)
      · left; rw [h]; group
      · right; rw [h, hxe0]
  have hd : x * q * x⁻¹ * q⁻¹ ∈ Subgroup.zpowers e0 := by
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x * q * x⁻¹, hxq⟩)
      (b := ⟨q⁻¹, inv_mem hq⟩)).mpr (by
        simp only [Subgroup.mem_subgroupOf]
        rw [hiff]
        exact ⟨fun h => inv_mem h, fun h => by simpa using inv_mem h⟩)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  rcases (hmemz _).mp hd with h | h
  · calc x * q * x⁻¹ = (x * q * x⁻¹ * q⁻¹) * q := by group
      _ = q := by rw [h]; group
  · exfalso
    apply he01
    have h1 : x * q * x⁻¹ = e0 * q := by rw [← h]; group
    have h2 : x * (x * q * x⁻¹) * x⁻¹ = q := by
      rw [h1, show x * (e0 * q) * x⁻¹ = (x * e0 * x⁻¹) * (x * q * x⁻¹) by group, hxe0, h1,
        ← mul_assoc, he0sq, one_mul]
    have h3 := hcube q
    rw [h2, h1] at h3
    calc e0 = (e0 * q) * q⁻¹ := by group
      _ = 1 := by rw [h3]; group

end CFSG.Quasithin.E6.A3Push
