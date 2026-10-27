module

public import CFSG.RankThree.GF2n.Parrott.Section5KLUVOrbit
public import CFSG.GroupTheory.CommuteOfSqEqOne

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

private theorem mem_closure_t_uv_iff_kl (q : A45) :
    q ∈ Subgroup.closure ({tA, uA * vA} : Set A45) ↔
      q = 1 ∨ q = tA ∨ q = uA * vA ∨ q = tA * (uA * vA) := by
  constructor
  · intro hq
    let S : Subgroup A45 :=
      { carrier := {y | y = 1 ∨ y = tA ∨ y = uA * vA ∨ y = tA * (uA * vA)}
        one_mem' := Or.inl rfl
        mul_mem' := by
          intro y w hy hw
          simp only [Set.mem_setOf_eq] at hy hw ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            rcases hw with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one] <;>
            decide +kernel
        inv_mem' := by
          intro y hy
          simp only [Set.mem_setOf_eq] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] <;>
            decide +kernel }
    have hle : Subgroup.closure ({tA, uA * vA} : Set A45) ≤ S := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hq
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

omit [Finite G] in
private theorem lemma54T₂_le_H_kl {σ g : G} (hg : g ∈ lemma54T₂ D σ) : g ∈ H z :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1

omit [Finite G] in
private theorem mem_lemma54T₂_iff_kl {σ : G} {g : G} (hg : g ∈ H z) :
    g ∈ lemma54T₂ D σ ↔ g ∈ Subgroup.centralizer ({σ} : Set G) ∧
      qH (z := z) D ⟨g, hg⟩ ∈ Subgroup.closure ({tA, uA * vA} : Set A45) := by
  constructor
  · intro hmem
    rw [lemma54T₂] at hmem
    obtain ⟨hY, hmap⟩ := Subgroup.mem_inf.mp hmem
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmap
    rw [Subgroup.mem_comap] at hy
    refine ⟨(Subgroup.mem_inf.mp hY).2, ?_⟩
    have hyy : (⟨g, hg⟩ : ↥(H z)) = y := Subtype.ext hyx.symm
    rw [hyy]
    exact hy
  · rintro ⟨hσ, hK⟩
    rw [lemma54T₂]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hg, hσ⟩,
      Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr hK, rfl⟩⟩

omit hN in
private theorem conjV_pi_eq_of_conj_eq_kl (h : Tim79a.ParrottHyp z) {g : ↥(H z)} {b : J z}
    (hb : (g : G) * (b : G) * (g : G)⁻¹ = (b : G)) :
    conjV h g (QuotientV.pi z b) = QuotientV.pi z b := by
  rw [conjV_mk]
  rw [show conjJ' z g b = b from Subtype.ext (by rw [conjJ'_apply_coe]; exact hb)]

private theorem mul_inv_mul_mul_comm_kl {M : Type*} [Group M] (hcomm : ∀ x y : M, x * y = y * x)
    (a b c d : M) : (a * b)⁻¹ * (c * d) = (a⁻¹ * c) * (b⁻¹ * d) := by
  let : CommGroup M := { (inferInstance : Group M) with mul_comm := hcomm }
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem exists_mem_centerIn_lemma54T₂_inf_centralizer_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA) :
    ∃ a ∈ centerIn (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        centralizer ({(x : G)} : Set G)),
      a ≠ 1 ∧ a ≠ z ∧
      a ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ∧
      a * a = 1 ∧
      ∀ e ∈ centerIn (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
          centralizer ({(x : G)} : Set G)),
        e = 1 ∨ e = z ∨ e = a ∨ e = a * z ∨ ∃ c ∈ H z, c * (x : G) * c⁻¹ = e := by
  classical
  obtain ⟨k, hkσ, hkx, hqk⟩ :=
    exists_mem_centralizer_qH_eq_t_of_qH_eq_uv (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
      hxσ hx2 hqx
  let s : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let Cc : Subgroup G := (J z ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
    Subgroup.centralizer ({(x : G)} : Set G)
  let K0 : Subgroup G := lemma54T₂ D s ⊓ Subgroup.centralizer ({(x : G)} : Set G)
  let F : Subgroup G := Cc ⊓ Subgroup.centralizer ({(k : G)} : Set G)
  have hsH : s ∈ H z := (sigma1Nine (z := z) D * σ₂⁻¹).2
  have hCcmem : ∀ {g : G}, g ∈ Cc ↔ g ∈ J z ∧
      g ∈ Subgroup.centralizer ({s} : Set G) ∧
      g ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro g
    simp only [Cc, Subgroup.mem_inf]
    tauto
  have hK0mem : ∀ {g : G}, g ∈ K0 ↔ g ∈ lemma54T₂ D s ∧
      g ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro g
    simp only [K0, Subgroup.mem_inf]
  have hFmem : ∀ {g : G}, g ∈ F ↔ g ∈ Cc ∧
      g ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
    intro g
    simp only [F, Subgroup.mem_inf]
  have hxK0 : (x : G) ∈ K0 := by
    rw [hK0mem]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    rw [mem_lemma54T₂_iff_kl (z := z) D (hg := x.2)]
    refine ⟨hxσ, ?_⟩
    rw [show (⟨(x : G), x.2⟩ : ↥(H z)) = x from rfl, hqx]
    exact Subgroup.subset_closure (by simp)
  have hkK0 : (k : G) ∈ K0 := by
    rw [hK0mem]
    refine ⟨?_, hkx⟩
    rw [mem_lemma54T₂_iff_kl (z := z) D (hg := k.2)]
    refine ⟨hkσ, ?_⟩
    rw [show (⟨(k : G), k.2⟩ : ↥(H z)) = k from rfl, hqk]
    exact Subgroup.subset_closure (by simp)
  have hCK0 : Cc ≤ K0 := by
    intro c hc
    rw [hCcmem] at hc
    obtain ⟨hcJ, hcσ, hcx⟩ := hc
    rw [hK0mem]
    refine ⟨?_, hcx⟩
    rw [mem_lemma54T₂_iff_kl (z := z) D (hg := J_le_H hcJ)]
    refine ⟨hcσ, ?_⟩
    rw [(J_mem_iff D ⟨c, J_le_H hcJ⟩).mp (Subgroup.mem_subgroupOf.mpr hcJ)]
    exact Subgroup.one_mem _
  have hK0J : ∀ {e : G}, e ∈ K0 → e ∈ J z → e ∈ Cc := by
    intro e heK0 heJ
    rw [hK0mem] at heK0
    obtain ⟨heT2, hex⟩ := heK0
    obtain ⟨heσ, -⟩ := (mem_lemma54T₂_iff_kl (z := z) D (hg := lemma54T₂_le_H_kl D heT2)).mp heT2
    rw [hCcmem]
    exact ⟨heJ, heσ, hex⟩
  have hCcard : Nat.card ↥Cc = 8 := by
    have hcard := card_J_inf_centralizer_inf_centralizer_eq_eight (z := z) D h hZ hz₁ hz₁z hord
      P hP hσ₂ hq₂ hc₂ hxσ hx2 (Or.inl hqx)
    simpa only [Cc] using hcard
  have hFle4 : Nat.card ↥F ≤ 4 := by
    have hcard := card_centralizer_le_four_of_qH_eq_uv (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂
      hq₂ hc₂ hxσ hx2 hqx hqk
    simpa only [F, Cc] using hcard
  have hCsq : ∀ c ∈ Cc, c * c = 1 := by
    intro c hc
    rw [hCcmem] at hc
    obtain ⟨hcJ, hcσ, hcx⟩ := hc
    have hconj : (x : G) * c * (x : G)⁻¹ = c := by
      have h2 : c * (x : G) = (x : G) * c := Subgroup.mem_centralizer_singleton_iff.mp hcx
      rw [← h2]
      group
    exact mul_self_eq_one_of_conjV_pi_eq_of_qH_eq_uv (z := z) D h P hP hq₂ hqx
      (b := ⟨c, hcJ⟩) hcσ
      (conjV_pi_eq_of_conj_eq_kl (z := z) h (g := x) (b := ⟨c, hcJ⟩) hconj)
  have hCcomm : ∀ u ∈ Cc, ∀ v ∈ Cc, u * v = v * u := by
    intro u hu v hv
    have hu2 : u * u = 1 := hCsq u hu
    have hv2 : v * v = 1 := hCsq v hv
    have huv2 : (u * v) * (u * v) = 1 := hCsq (u * v) (Cc.mul_mem hu hv)
    exact commute_of_sq_eq_one (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact hv2)
      (by rw [pow_two]; exact huv2)
  have hkz : (k : G) * z = z * (k : G) :=
    Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (k : G) k.2
  have hzCc : z ∈ Cc := by
    rw [hCcmem]
    refine ⟨z_mem_J h, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) s hsH).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (x : G) x.2).symm
  have hαmem : ∀ c ∈ Cc, (k : G) * c * (k : G)⁻¹ ∈ Cc := by
    intro c hc
    rw [hCcmem] at hc ⊢
    obtain ⟨hcJ, hcσ, hcx⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · have hmem := (conjJ' z k ⟨c, hcJ⟩).2
      simpa only [conjJ'_apply_coe, Subgroup.coe_mk] using hmem
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hks : (k : G) * s = s * (k : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hkσ
      have hks' : (k : G)⁻¹ * s = s * (k : G)⁻¹ :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hkσ)
      have hcs : c * s = s * c := Subgroup.mem_centralizer_singleton_iff.mp hcσ
      calc (k : G) * c * (k : G)⁻¹ * s = (k : G) * c * ((k : G)⁻¹ * s) := by group
        _ = (k : G) * c * (s * (k : G)⁻¹) := by rw [hks']
        _ = (k : G) * (c * s) * (k : G)⁻¹ := by group
        _ = (k : G) * (s * c) * (k : G)⁻¹ := by rw [hcs]
        _ = ((k : G) * s) * c * (k : G)⁻¹ := by group
        _ = (s * (k : G)) * c * (k : G)⁻¹ := by rw [hks]
        _ = s * ((k : G) * c * (k : G)⁻¹) := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hks : (k : G) * (x : G) = (x : G) * (k : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hkx
      have hks' : (k : G)⁻¹ * (x : G) = (x : G) * (k : G)⁻¹ :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hkx)
      have hcs : c * (x : G) = (x : G) * c := Subgroup.mem_centralizer_singleton_iff.mp hcx
      calc (k : G) * c * (k : G)⁻¹ * (x : G) = (k : G) * c * ((k : G)⁻¹ * (x : G)) := by group
        _ = (k : G) * c * ((x : G) * (k : G)⁻¹) := by rw [hks']
        _ = (k : G) * (c * (x : G)) * (k : G)⁻¹ := by group
        _ = (k : G) * ((x : G) * c) * (k : G)⁻¹ := by rw [hcs]
        _ = ((k : G) * (x : G)) * c * (k : G)⁻¹ := by group
        _ = ((x : G) * (k : G)) * c * (k : G)⁻¹ := by rw [hks]
        _ = (x : G) * ((k : G) * c * (k : G)⁻¹) := by group
  let α : ↥Cc →* ↥Cc :=
    { toFun := fun c => ⟨(k : G) * (c : G) * (k : G)⁻¹, hαmem c c.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hαcoe : ∀ c : ↥Cc, ((α c : ↥Cc) : G) = (k : G) * (c : G) * (k : G)⁻¹ := fun c => rfl
  have hk2Cc : (k : G) * (k : G) ∈ Cc := by
    rw [hCcmem]
    refine ⟨?_, ?_, ?_⟩
    · have hq : qH (z := z) D ⟨(k : G) * (k : G), (H z).mul_mem k.2 k.2⟩ = 1 := by
        have hkk : (⟨(k : G) * (k : G), (H z).mul_mem k.2 k.2⟩ : ↥(H z)) = k * k :=
          Subtype.ext rfl
        rw [hkk, map_mul, hqk]
        exact Subtype.ext t_sq
      exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hq)
    · exact Subgroup.mul_mem _ hkσ hkσ
    · exact Subgroup.mul_mem _ hkx hkx
  have hCinv : ∀ c : ↥Cc, c⁻¹ = c := by
    intro c
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    exact hCsq c c.2
  have hCcomm' : ∀ x y : ↥Cc, x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact hCcomm x x.2 y y.2
  have hαα : ∀ c : ↥Cc, α (α c) = c := by
    intro c
    apply Subtype.ext
    show (k : G) * ((k : G) * (c : G) * (k : G)⁻¹) * (k : G)⁻¹ = (c : G)
    have hcomm : ((k : G) * (k : G)) * (c : G) = (c : G) * ((k : G) * (k : G)) :=
      hCcomm _ hk2Cc _ c.2
    calc (k : G) * ((k : G) * (c : G) * (k : G)⁻¹) * (k : G)⁻¹
        = ((k : G) * (k : G)) * (c : G) * ((k : G) * (k : G))⁻¹ := by group
      _ = (c : G) := by rw [hcomm]; group
  let ψ : ↥Cc →* ↥Cc :=
    { toFun := fun c => c⁻¹ * α c
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        show (a * b)⁻¹ * α (a * b) = (a⁻¹ * α a) * (b⁻¹ * α b)
        rw [map_mul]
        exact mul_inv_mul_mul_comm_kl hCcomm' a b (α a) (α b) }
  have hψfix : ∀ c : ↥Cc, α (ψ c) = ψ c := by
    intro c
    calc α (ψ c) = α (c⁻¹ * α c) := rfl
      _ = (α c)⁻¹ * α (α c) := by rw [map_mul, map_inv]
      _ = (α c)⁻¹ * c := by rw [hαα]
      _ = (α c) * c := by rw [hCinv (α c)]
      _ = c * (α c) := hCcomm' (α c) c
      _ = c⁻¹ * (α c) := by rw [hCinv c]
      _ = ψ c := rfl
  have hψψ : ∀ c : ↥Cc, ψ (ψ c) = 1 := by
    intro c
    show (ψ c)⁻¹ * α (ψ c) = 1
    rw [hψfix c, inv_mul_cancel]
  have hrange_le : ψ.range ≤ ψ.ker := by
    rintro y ⟨c, rfl⟩
    exact MonoidHom.mem_ker.mpr (hψψ c)
  have hker_ge : 3 ≤ Nat.card ↥ψ.ker := by
    have hkr := Subgroup.card_ker_mul_card_range ψ
    have hle : Nat.card ↥ψ.range ≤ Nat.card ↥ψ.ker :=
      Nat.card_le_card_of_injective (fun y : ↥ψ.range => (⟨(y : ↥Cc), hrange_le y.2⟩ : ↥ψ.ker))
        (by
          intro y y' h
          exact Subtype.ext (congrArg (fun y : ↥ψ.ker => (y : ↥Cc)) h))
    have hmul : Nat.card ↥Cc ≤ Nat.card ↥ψ.ker * Nat.card ↥ψ.ker := by
      rw [← hkr]
      exact Nat.mul_le_mul_left _ hle
    rw [hCcard] at hmul
    by_contra hcon
    have h2 : Nat.card ↥ψ.ker ≤ 2 := by omega
    have h4 : Nat.card ↥ψ.ker * Nat.card ↥ψ.ker ≤ 2 * 2 := Nat.mul_le_mul h2 h2
    omega
  let zc : ↥Cc := ⟨z, hzCc⟩
  have hex : ∃ a : ↥Cc, a ∈ ψ.ker ∧ (a : G) ≠ 1 ∧ (a : G) ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : (ψ.ker : Set ↥Cc) ⊆ (({1, zc} : Finset ↥Cc) : Set ↥Cc) := by
      intro y hy
      rcases eq_or_ne (y : G) 1 with h | h
      · have hy1 : y = 1 := by
          apply Subtype.ext
          show (y : G) = 1
          exact h
        rw [hy1]
        simp
      · have hyz : y = zc := by
          apply Subtype.ext
          show (y : G) = z
          exact hcon y hy h
        rw [hyz]
        simp
    have hle2 : Nat.card ↥ψ.ker ≤ 2 := by
      change (ψ.ker : Set ↥Cc).ncard ≤ 2
      calc (ψ.ker : Set ↥Cc).ncard
          ≤ (({1, zc} : Finset ↥Cc) : Set ↥Cc).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = ({1, zc} : Finset ↥Cc).card := Set.ncard_coe_finset _
        _ ≤ 2 := by
            have hc := Finset.card_insert_le (1 : ↥Cc) ({zc} : Finset ↥Cc)
            simp only [Finset.card_singleton] at hc
            omega
    omega
  obtain ⟨a, ha_ker, ha1, haz⟩ := hex
  have hαa : α a = a := by
    have hker : a⁻¹ * α a = 1 := ha_ker
    calc α a = a * (a⁻¹ * α a) := by group
      _ = a * 1 := by rw [hker]
      _ = a := mul_one a
  have haCcmem : (a : G) ∈ J z ∧ (a : G) ∈ Subgroup.centralizer ({s} : Set G) ∧
      (a : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := hCcmem.mp a.2
  have haF : (a : G) ∈ F := by
    rw [hFmem]
    refine ⟨a.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hαaeq : (k : G) * (a : G) * (k : G)⁻¹ = (a : G) := by
      rw [← hαcoe a, hαa]
    calc (a : G) * (k : G) = ((k : G) * (a : G) * (k : G)⁻¹) * (k : G) := by rw [hαaeq]
      _ = (k : G) * (a : G) := by group
  have ha2 : (a : G) * (a : G) = 1 := hCsq (a : G) a.2
  have hzF : z ∈ F := by
    rw [hFmem]
    refine ⟨hzCc, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hkz.symm
  have hz2 : z * z = 1 := by
    have hh := pow_orderOf_eq_one z
    rw [h.1, pow_two] at hh
    exact hh
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 := h.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have haz1 : (a : G) * z ≠ 1 := by
    intro h1
    apply haz
    calc (a : G) = ((a : G) * z) * z := by rw [mul_assoc, hz2, mul_one]
      _ = z := by rw [h1, one_mul]
  have h1az : (1 : G) ≠ (a : G) * z := fun h1 => haz1 h1.symm
  have hzaz : z ≠ (a : G) * z := by
    intro h1
    apply ha1
    calc (a : G) = ((a : G) * z) * z := by rw [mul_assoc, hz2, mul_one]
      _ = z * z := by rw [← h1]
      _ = 1 := hz2
  have hazaz : (a : G) ≠ (a : G) * z := by
    intro h1
    apply hz1
    calc z = (a : G)⁻¹ * ((a : G) * z) := by rw [inv_mul_cancel_left]
      _ = (a : G)⁻¹ * (a : G) := by rw [← h1]
      _ = 1 := inv_mul_cancel _
  have h4sub : (({1, z, (a : G), (a : G) * z} : Finset G) : Set G) ⊆ (F : Set G) := by
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact F.one_mem
    · exact hzF
    · exact haF
    · exact F.mul_mem haF hzF
  have h4card : (({1, z, (a : G), (a : G) * z} : Finset G) : Set G).ncard = 4 := by
    rw [Set.ncard_coe_finset]
    have hc : ({1, z, (a : G), (a : G) * z} : Finset G).card = 4 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hz1.symm, ha1.symm, h1az⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨haz.symm, hzaz⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact hazaz),
          Finset.card_singleton]
    exact hc
  have hFeq : (F : Set G) = (({1, z, (a : G), (a : G) * z} : Finset G) : Set G) := by
    symm
    apply Set.eq_of_subset_of_ncard_le h4sub
    rw [h4card, ← Nat.card_coe_set_eq]
    exact hFle4
  have hFcases : ∀ e ∈ F, e = 1 ∨ e = z ∨ e = (a : G) ∨ e = (a : G) * z := by
    intro e he
    have he' : e ∈ (({1, z, (a : G), (a : G) * z} : Finset G) : Set G) := hFeq ▸ he
    simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using he'
  have hdecomp : ∀ g ∈ K0, ∃ l : G,
      (l = 1 ∨ l = (k : G) ∨ l = (x : G) ∨ l = (k : G) * (x : G)) ∧
      ∃ c ∈ Cc, g = l * c := by
    intro g hg
    rw [hK0mem] at hg
    obtain ⟨hgT2, hgx⟩ := hg
    have hgH : g ∈ H z := lemma54T₂_le_H_kl D hgT2
    obtain ⟨hgσ, hgK⟩ :=
      (mem_lemma54T₂_iff_kl (z := z) D (hg := hgH)).mp hgT2
    let gg : ↥(H z) := ⟨g, hgH⟩
    have hstep : ∀ l : ↥(H z), qH D l = qH D gg →
        (l : G) ∈ Subgroup.centralizer ({s} : Set G) →
        (l : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) →
        ∃ c ∈ Cc, g = (l : G) * c := by
      intro l hl hlσ hlx
      have hq1 : qH D (l⁻¹ * gg) = 1 := by rw [map_mul, map_inv, hl, inv_mul_cancel]
      have hcJ : ((l⁻¹ * gg : ↥(H z)) : G) ∈ J z :=
        Subgroup.mem_subgroupOf.mp ((J_mem_iff D (l⁻¹ * gg)).mpr hq1)
      have hcσ : ((l⁻¹ * gg : ↥(H z)) : G) ∈ Subgroup.centralizer ({s} : Set G) := by
        have hcoe : ((l⁻¹ * gg : ↥(H z)) : G) = (l : G)⁻¹ * (gg : G) := rfl
        rw [hcoe]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hlσ) hgσ
      have hcx : ((l⁻¹ * gg : ↥(H z)) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
        have hcoe : ((l⁻¹ * gg : ↥(H z)) : G) = (l : G)⁻¹ * (gg : G) := rfl
        rw [hcoe]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hlx) hgx
      refine ⟨((l⁻¹ * gg : ↥(H z)) : G), ?_, ?_⟩
      · rw [hCcmem]
        exact ⟨hcJ, hcσ, hcx⟩
      · show g = (l : G) * ((l : G)⁻¹ * g)
        group
    have hxCx : (x : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rcases (mem_closure_t_uv_iff_kl (qH D gg)).mp hgK with h1 | h1 | h1 | h1
    · obtain ⟨c, hc, hgc⟩ := hstep 1 (by rw [h1]; simp) (Subgroup.one_mem _)
        (Subgroup.one_mem _)
      exact ⟨1, Or.inl rfl, c, hc, hgc⟩
    · obtain ⟨c, hc, hgc⟩ := hstep k (by rw [hqk, h1]) hkσ hkx
      exact ⟨(k : G), Or.inr (Or.inl rfl), c, hc, hgc⟩
    · obtain ⟨c, hc, hgc⟩ := hstep x (by rw [hqx, h1]) hxσ hxCx
      exact ⟨(x : G), Or.inr (Or.inr (Or.inl rfl)), c, hc, hgc⟩
    · obtain ⟨c, hc, hgc⟩ := hstep (k * x) (by rw [map_mul, hqk, hqx, h1])
        (Subgroup.mul_mem _ hkσ hxσ) (Subgroup.mul_mem _ hkx hxCx)
      exact ⟨(k : G) * (x : G), Or.inr (Or.inr (Or.inr rfl)), c, hc, by rw [hgc]; rfl⟩
  have haCenter : (a : G) ∈ centerIn K0 := by
    show (a : G) ∈ K0 ⊓ Subgroup.centralizer (K0 : Set G)
    have hacent : (a : G) ∈ Subgroup.centralizer (K0 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨l, hl, c, hcC, hg_eq⟩ := hdecomp g hg
      have hac : (a : G) * c = c * (a : G) := hCcomm (a : G) a.2 c hcC
      have hal : (a : G) * l = l * (a : G) := by
        rcases hl with rfl | rfl | rfl | rfl
        · simp
        · exact Subgroup.mem_centralizer_singleton_iff.mp haF.2
        · exact Subgroup.mem_centralizer_singleton_iff.mp haCcmem.2.2
        · calc (a : G) * ((k : G) * (x : G)) = ((a : G) * (k : G)) * (x : G) := by
                rw [mul_assoc]
            _ = ((k : G) * (a : G)) * (x : G) := by
                rw [Subgroup.mem_centralizer_singleton_iff.mp haF.2]
            _ = (k : G) * ((a : G) * (x : G)) := by rw [mul_assoc]
            _ = (k : G) * ((x : G) * (a : G)) := by
                rw [Subgroup.mem_centralizer_singleton_iff.mp haCcmem.2.2]
            _ = ((k : G) * (x : G)) * (a : G) := by rw [mul_assoc]
      calc g * (a : G) = (l * c) * (a : G) := by rw [hg_eq]
        _ = l * (c * (a : G)) := by group
        _ = l * ((a : G) * c) := by rw [← hac]
        _ = (l * (a : G)) * c := by group
        _ = ((a : G) * l) * c := by rw [hal]
        _ = (a : G) * (l * c) := by group
        _ = (a : G) * g := by rw [hg_eq]
    exact Subgroup.mem_inf.mpr ⟨hCK0 a.2, hacent⟩
  refine ⟨(a : G), haCenter, ha1, haz, ⟨haCcmem.1, haCcmem.2.1⟩, ha2, ?_⟩
  intro e he
  have he' : e ∈ K0 ⊓ Subgroup.centralizer (K0 : Set G) := he
  obtain ⟨heK0, heCent⟩ := Subgroup.mem_inf.mp he'
  have heH : e ∈ H z := lemma54T₂_le_H_kl D (Subgroup.mem_inf.mp heK0).1
  let eg : ↥(H z) := ⟨e, heH⟩
  by_cases hqe : qH (z := z) D eg = 1
  ·
    have heJ : e ∈ J z :=
      Subgroup.mem_subgroupOf.mp ((J_mem_iff D eg).mpr hqe)
    have heCc : e ∈ Cc := hK0J heK0 heJ
    have heF : e ∈ F := by
      rw [hFmem]
      refine ⟨heCc, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp heCent (k : G) hkK0).symm
    rcases hFcases e heF with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  ·
    obtain ⟨heσ, -⟩ := (mem_lemma54T₂_iff_kl (z := z) D (hg := heH)).mp
      (Subgroup.mem_inf.mp heK0).1
    have hex : e ∈ Subgroup.centralizer ({(x : G)} : Set G) := (Subgroup.mem_inf.mp heK0).2
    have hecomm : ∀ c ∈ (J z ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
        Subgroup.centralizer ({(x : G)} : Set G), (eg : G) * c = c * (eg : G) := by
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp heCent c (hCK0 hc)).symm
    have hne := qH_ne_t_of_forall_commute_of_qH_eq_uv (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂
      hq₂ hc₂ hxσ hx2 hqx hecomm
    have hqmem : qH D eg ∈ Subgroup.closure ({tA, uA * vA} : Set A45) :=
      ((mem_lemma54T₂_iff_kl (z := z) D (hg := heH)).mp
        (Subgroup.mem_inf.mp heK0).1).2
    rcases (mem_closure_t_uv_iff_kl (qH D eg)).mp hqmem with h1 | h1 | h1 | h1
    · exact absurd h1 hqe
    · exact absurd h1 hne.1
    · have hxinvx : (x : G)⁻¹ ∈ Subgroup.centralizer ({(x : G)} : Set G) :=
        Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      have hqec : qH (z := z) D (x⁻¹ * eg) = 1 := by
        rw [map_mul, map_inv, hqx, h1, inv_mul_cancel]
      have hecJ : ((x⁻¹ * eg : ↥(H z)) : G) ∈ J z :=
        Subgroup.mem_subgroupOf.mp ((J_mem_iff D (x⁻¹ * eg)).mpr hqec)
      have hecσ : ((x⁻¹ * eg : ↥(H z)) : G) ∈ Subgroup.centralizer ({s} : Set G) := by
        have hcoe : ((x⁻¹ * eg : ↥(H z)) : G) = (x : G)⁻¹ * e := rfl
        rw [hcoe]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxσ) heσ
      have hecx : ((x⁻¹ * eg : ↥(H z)) : G) ∈
          Subgroup.centralizer ({(x : G)} : Set G) := by
        have hcoe : ((x⁻¹ * eg : ↥(H z)) : G) = (x : G)⁻¹ * e := rfl
        rw [hcoe]
        exact Subgroup.mul_mem _ hxinvx hex
      have hecCc : ((x⁻¹ * eg : ↥(H z)) : G) ∈ Cc := by
        rw [hCcmem]
        exact ⟨hecJ, hecσ, hecx⟩
      obtain ⟨q, hq, hqeq⟩ := exists_conj_eq_mul_of_qH_eq_uv (z := z) D h hZ hz₁ hz₁z hord P hP
        hσ₂ hq₂ hc₂ hxσ hx2 hqx hecCc
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨q, J_le_H (Subgroup.mem_inf.mp hq).1, ?_⟩)))
      calc q * (x : G) * q⁻¹ = (x : G) * ((x⁻¹ * eg : ↥(H z)) : G) := hqeq
        _ = (x : G) * ((x : G)⁻¹ * e) := by
            rw [show ((x⁻¹ * eg : ↥(H z)) : G) = (x : G)⁻¹ * e from rfl]
        _ = e := by group
    · exact absurd h1 hne.2

end CFSG.RankThree.GF2n.Parrott
