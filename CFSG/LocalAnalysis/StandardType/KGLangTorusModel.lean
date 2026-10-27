module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
import CFSG.LocalAnalysis.StandardType.KGLangH90PPart

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma kgLangModelAux_kgInducedAut_apply_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) =
    θ (QuotientGroup.mk (α k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerQuotAut_mk]

private theorem kgLangModelAux_eq_one_of_mem_center_of_pow {K : Type*} [Group K] {p : ℕ}
    (hp : p.Prime) (hZ : Nat.Coprime (Nat.card (Subgroup.center K)) p) {d : K}
    (hd : d ∈ Subgroup.center K) (hdp : ∃ k : ℕ, d ^ p ^ k = 1) : d = 1 := by
  obtain ⟨k, hk⟩ := hdp
  have h1 : orderOf d ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
  have h2 : p ^ j ∣ Nat.card (Subgroup.center K) := by
    rw [← hj]
    exact Subgroup.orderOf_dvd_natCard _ hd
  have hcop : Nat.Coprime (p ^ j) (Nat.card (Subgroup.center K)) := hZ.symm.pow_left j
  have hj1 : p ^ j = 1 := hcop.eq_one_of_dvd h2
  exact orderOf_eq_one_iff.mp (by rw [hj, hj1])

theorem kgLangDescent {p : ℕ} (hp : p.Prime) {K R : Type} [Group K] [Finite K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hZ : Nat.Coprime (Nat.card (Subgroup.center K)) p)
    (I : Set (MulAut R)) (A : Subgroup (MulAut K)) (α₀ : MulAut K) (Mb : Subgroup R)
    (hMab : ∀ a ∈ Mb, ∀ b ∈ Mb, a * b = b * a) (hMp : ∀ x ∈ Mb, ∃ k : ℕ, x ^ p ^ k = 1)
    (hMst : ∀ r, kgInducedAut θ α₀ r ∈ Mb ↔ r ∈ Mb)
    (hMfix : ∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ r ∈ Mb, kgInducedAut θ α r = r)
    (hM90 : ∀ c ∈ Mb, ((List.range p).map fun i => (kgInducedAut θ α₀ ^ i) c).prod = 1 →
      ∃ s ∈ Mb, c = s⁻¹ * kgInducedAut θ α₀ s)
    (eb : R) (heb : eb ∈ Mb) (heb1 : eb ≠ 1) (hebp : eb ^ p = 1) (hebα : kgInducedAut θ α₀ eb = eb) :
    ∃ M : Subgroup K, (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧
      (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t) ∧
      (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 → ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
      ∃ e ∈ M, e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e ∧ ∀ α ∈ A, kgInducedAut θ α ∈ I → α e = e := by
  letI : Bracket K K := commutatorElement
  let π : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ_apply : ∀ x : K, π x = θ (QuotientGroup.mk x) := fun _ => rfl
  have hπker : ∀ x : K, π x = 1 ↔ x ∈ Subgroup.center K := by
    intro x
    rw [hπ_apply]
    constructor
    · intro hx
      have h1 : QuotientGroup.mk x = 1 := θ.injective (by rw [hx, map_one])
      rwa [QuotientGroup.eq_one_iff] at h1
    · intro hx
      rw [show QuotientGroup.mk x = (1 : K ⧸ Subgroup.center K) from
        (QuotientGroup.eq_one_iff x).mpr hx, map_one]
  have hπα : ∀ (α : MulAut K) (x : K), π (α x) = kgInducedAut θ α (π x) := by
    intro α x
    rw [hπ_apply, hπ_apply]
    exact (kgLangModelAux_kgInducedAut_apply_mk θ α x).symm
  let P : Subgroup K := Mb.comap π
  have mem_P : ∀ x : K, x ∈ P ↔ π x ∈ Mb := fun _ => Subgroup.mem_comap
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro x hx y hy
    have hxMb : π x ∈ Mb := (mem_P x).mp hx
    have hyMb : π y ∈ Mb := (mem_P y).mp hy
    have hc_center : ⁅x, y⁆ ∈ Subgroup.center K := by
      rw [← hπker]
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hMab (π x) hxMb (π y) hyMb)
    obtain ⟨k, hk⟩ := hMp (π y) hyMb
    have hyk_center : y ^ p ^ k ∈ Subgroup.center K := by
      rw [← hπker]
      rw [map_pow, hk]
    have h1 : ⁅x, y ^ p ^ k⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp hyk_center x
    have h2 : ⁅x, y⁆ ^ p ^ k = ⁅x, y ^ p ^ k⁆ := by
      have hcy : Commute y ⁅x, y⁆ :=
        Subgroup.mem_center_iff.mp hc_center y
      exact hcy.commutatorElement_pow_right (p ^ k)
    have hc1 : ⁅x, y⁆ = 1 :=
      kgLangModelAux_eq_one_of_mem_center_of_pow hp hZ hc_center ⟨k, by rw [h2, h1]⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1
  letI : CommGroup P := CommGroup.mk fun a b => Subtype.ext (hPab a a.2 b b.2)
  let M : Subgroup K := (CommGroup.primaryComponent P p).map P.subtype
  have mem_M : ∀ x : K, x ∈ M ↔ x ∈ P ∧ ∃ k : ℕ, x ^ p ^ k = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨y.2, ?_⟩
      obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp hy
      exact ⟨k, by simpa using congrArg (fun w : P => (w : K)) hk⟩
    · rintro ⟨hxP, k, hk⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
      exact CommGroup.mem_primaryComponent.mpr ⟨k, by
        apply Subtype.ext
        simpa using hk⟩
  have hMab' : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := fun a ha b hb =>
    hPab a ((mem_M a).mp ha).1 b ((mem_M b).mp hb).1
  have hMst' : ∀ t, α₀ t ∈ M ↔ t ∈ M := by
    intro t
    rw [mem_M, mem_M]
    constructor
    · rintro ⟨hαtP, k, hk⟩
      refine ⟨?_, k, ?_⟩
      · rw [mem_P] at hαtP ⊢
        rw [hπα] at hαtP
        exact (hMst (π t)).mp hαtP
      · have h : α₀ (t ^ p ^ k) = 1 := by rw [map_pow, hk]
        exact α₀.injective (by rw [h, map_one])
    · rintro ⟨htP, k, hk⟩
      refine ⟨?_, k, ?_⟩
      · rw [mem_P] at htP ⊢
        rw [hπα]
        exact (hMst (π t)).mpr htP
      · rw [← map_pow, hk, map_one]
  have hπinj : ∀ a ∈ M, ∀ b ∈ M, π a = π b → a = b := by
    intro a ha b hb hab
    have hd_center : a⁻¹ * b ∈ Subgroup.center K := by
      rw [← hπker]
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hdM : a⁻¹ * b ∈ M := M.mul_mem (M.inv_mem ha) hb
    exact inv_mul_eq_one.mp
      (kgLangModelAux_eq_one_of_mem_center_of_pow hp hZ hd_center ((mem_M _).mp hdM).2)
  have hπsurj : Function.Surjective π := by
    intro r
    obtain ⟨y, hy⟩ := θ.surjective r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) y
    exact ⟨x, by rw [hπ_apply]; simpa using hy⟩
  have hMb_dvd : Nat.card Mb ∣ Nat.card P := by
    have hrange : (π.comp P.subtype).range = Mb := by
      apply le_antisymm
      · rintro r ⟨x, rfl⟩
        exact (mem_P x).mp x.2
      · intro r hr
        obtain ⟨x, hx⟩ := hπsurj r
        exact ⟨⟨x, (mem_P x).mpr (by rw [hx]; exact hr)⟩, hx⟩
    have hcard := Subgroup.card_ker_mul_card_range (π.comp P.subtype)
    rw [hrange] at hcard
    exact ⟨Nat.card (π.comp P.subtype).ker, by rw [← hcard, mul_comm]⟩
  have hMsurj : ∀ s ∈ Mb, ∃ s' ∈ M, π s' = s := by
    have hn : Nat.card P ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
    have hcopm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
    have hcop : Nat.Coprime m (p ^ a) := hcopm.symm.pow_right a
    have ht_exists : ∃ t, m * t ≡ 1 [MOD p ^ a] := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; exact ⟨0, by simp [Nat.ModEq]⟩
      · have hlt : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
        obtain ⟨t, _, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
        exact ⟨t, by rw [Nat.ModEq, ht, Nat.mod_eq_of_lt hlt]⟩
    obtain ⟨t, hmt⟩ := ht_exists
    intro s hsMb
    obtain ⟨x, hx⟩ := hπsurj s
    have hxP : x ∈ P := (mem_P x).mpr (by rw [hx]; exact hsMb)
    obtain ⟨k, hk⟩ := hMp s hsMb
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_iff_pow_eq_one.mpr hk)
    have hj_dvd_Mb : p ^ j ∣ Nat.card Mb := by
      rw [← hj]
      exact Subgroup.orderOf_dvd_natCard _ hsMb
    have hj_dvd_P : p ^ j ∣ Nat.card P := dvd_trans hj_dvd_Mb hMb_dvd
    have hj_dvd_pa : p ^ j ∣ p ^ a := by
      rw [hnm] at hj_dvd_P
      exact (hcopm.pow_left j).dvd_of_dvd_mul_right hj_dvd_P
    have hsm : s ^ (m * t) = s := by
      rw [pow_eq_pow_of_modEq hmt (orderOf_dvd_iff_pow_eq_one.mp (by rw [hj]; exact hj_dvd_pa)),
        pow_one]
    refine ⟨x ^ (m * t), ?_, ?_⟩
    · rw [mem_M]
      refine ⟨P.pow_mem hxP _, ⟨a, ?_⟩⟩
      rw [← pow_mul]
      have harith : m * t * p ^ a = t * (p ^ a * m) := by
        rw [mul_comm m t, mul_assoc t m (p ^ a), mul_comm m (p ^ a)]
      rw [harith, ← hnm, mul_comm t (Nat.card P), pow_mul,
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hxP), one_pow]
    · rw [map_pow, hx, hsm]
  have hM90' : ∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 →
      ∃ s ∈ M, c = s⁻¹ * α₀ s := by
    intro c hc hcn
    have hcP : c ∈ P := (mem_M c).mp hc |>.1
    have hπcMb : π c ∈ Mb := (mem_P c).mp hcP
    have hnorm : ((List.range p).map fun i => (kgInducedAut θ α₀ ^ i) (π c)).prod = 1 := by
      have hnorm' : ∀ i (x : K), π ((α₀ ^ i) x) = (kgInducedAut θ α₀ ^ i) (π x) := by
        intro i
        induction i with
        | zero => intro x; simp
        | succ i ih =>
          intro x
          rw [pow_succ, MulAut.mul_apply, ih, hπα, pow_succ, MulAut.mul_apply]
      have hlist : (List.map π ((List.range p).map fun i => (α₀ ^ i) c))
          = List.map (fun i => (kgInducedAut θ α₀ ^ i) (π c)) (List.range p) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hnorm' i c
      have h := congrArg π hcn
      rw [map_list_prod, map_one, hlist] at h
      exact h
    obtain ⟨s, hsMb, hs⟩ := hM90 (π c) hπcMb hnorm
    obtain ⟨s', hs'M, hs'⟩ := hMsurj s hsMb
    refine ⟨s', hs'M, ?_⟩
    apply hπinj c hc (s'⁻¹ * α₀ s')
      (M.mul_mem (M.inv_mem hs'M) ((hMst' s').mpr hs'M))
    rw [map_mul, map_inv, hs', hπα, hs', hs]
  have hMfixM : ∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t := by
    intro α hα hI t ht
    have htP : t ∈ P := (mem_M t).mp ht |>.1
    have hαtP : α t ∈ P := by
      rw [mem_P] at htP ⊢
      rw [hπα, hMfix α hα hI (π t) htP]
      exact htP
    have hαtM : α t ∈ M := by
      rw [mem_M]
      refine ⟨hαtP, ?_⟩
      obtain ⟨k, hk⟩ := (mem_M t).mp ht |>.2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    have hdM : t⁻¹ * α t ∈ M := M.mul_mem (M.inv_mem ht) hαtM
    have hd_center : t⁻¹ * α t ∈ Subgroup.center K := by
      rw [← hπker]
      rw [map_mul, map_inv]
      have hπt : π (α t) = π t := by rw [hπα, hMfix α hα hI (π t) htP]
      rw [hπt, inv_mul_cancel]
    exact (inv_mul_eq_one.mp
      (kgLangModelAux_eq_one_of_mem_center_of_pow hp hZ hd_center ((mem_M _).mp hdM).2)).symm
  obtain ⟨e, heM, heπ⟩ := hMsurj eb heb
  refine ⟨M, hMab', hMst', hMfixM, hM90', e, heM, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact heb1 (by rw [← heπ, h1, map_one])
  · have hepM : e ^ p ∈ M := M.pow_mem heM p
    have hep_center : e ^ p ∈ Subgroup.center K := by
      rw [← hπker]
      rw [map_pow, heπ, hebp]
    exact kgLangModelAux_eq_one_of_mem_center_of_pow hp hZ hep_center ((mem_M _).mp hepM).2
  · apply hπinj (α₀ e) ((hMst' e).mpr heM) e heM
    rw [hπα, heπ, hebα]
  · intro α hα hI
    exact hMfixM α hα hI e heM

theorem kgLangLT5_of_model {p : ℕ} (hp : p.Prime) {K R G : Type} [Group K] [Finite K] [Group R]
    [Group G] [Finite G]
    (θ : K ⧸ Subgroup.center K ≃* R) (hZ : Nat.Coprime (Nat.card (Subgroup.center K)) p)
    (I : Set (MulAut R)) (A : Subgroup (MulAut K)) (α₀ : MulAut K)
    (ι : R →* G) (hι : Function.Injective ι)
    (hG1 : ∀ g : G, ∀ k : ℕ, g ^ (p ^ k) = 1 → g ∈ ι.range)
    (β : MulAut G) (hβι : ∀ r, ι (kgInducedAut θ α₀ r) = β (ι r))
    (N : Subgroup G) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hβN : ∀ g, β g ∈ N ↔ g ∈ N)
    (hH90 : ∀ c ∈ N, ((List.range p).map fun i => (β ^ i) c).prod = 1 →
      ∃ s ∈ N, c = s⁻¹ * β s)
    (h : MulAut K → G)
    (hh : ∀ α ∈ A, kgInducedAut θ α ∈ I → h α ∈ N ∧ h α ^ p = 1 ∧ β (h α) = h α ∧
      ∀ r, ι (kgInducedAut θ α r) = h α * ι r * (h α)⁻¹)
    (hne : ∃ α ∈ A, kgInducedAut θ α ∈ I ∧ h α ≠ 1) :
    ∃ M : Subgroup K, (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧
      (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t) ∧
      (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 →
        ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
      ∃ e ∈ M, e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e ∧
        ∀ α ∈ A, kgInducedAut θ α ∈ I → α e = e := by
  letI : CommGroup N := CommGroup.mk fun a b => Subtype.ext (hNab a a.2 b b.2)
  let Np : Subgroup G := (CommGroup.primaryComponent N p).map N.subtype
  let Mb : Subgroup R := Np.comap ι
  have mem_Np : ∀ y : G, y ∈ Np ↔ y ∈ N ∧ ∃ k : ℕ, y ^ p ^ k = 1 := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      refine ⟨z.2, ?_⟩
      obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp hz
      exact ⟨k, by simpa using congrArg (fun w : N => (w : G)) hk⟩
    · rintro ⟨hyN, k, hk⟩
      refine Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, ?_, rfl⟩
      exact CommGroup.mem_primaryComponent.mpr ⟨k, by
        apply Subtype.ext
        simpa using hk⟩
  have mem_Mb : ∀ r : R, r ∈ Mb ↔ ι r ∈ N ∧ ∃ k : ℕ, (ι r) ^ p ^ k = 1 := by
    intro r
    rw [Subgroup.mem_comap, mem_Np]
  have hMab : ∀ a ∈ Mb, ∀ b ∈ Mb, a * b = b * a := by
    intro a ha b hb
    apply hι
    rw [map_mul, map_mul]
    exact hNab (ι a) ((mem_Mb a).mp ha).1 (ι b) ((mem_Mb b).mp hb).1
  have hMp : ∀ x ∈ Mb, ∃ k : ℕ, x ^ p ^ k = 1 := by
    intro x hx
    obtain ⟨-, k, hk⟩ := (mem_Mb x).mp hx
    refine ⟨k, ?_⟩
    apply hι
    rw [map_pow, map_one, hk]
  have hMst : ∀ r, kgInducedAut θ α₀ r ∈ Mb ↔ r ∈ Mb := by
    intro r
    rw [mem_Mb, mem_Mb, hβι r]
    constructor
    · rintro ⟨hN, k, hk⟩
      refine ⟨(hβN (ι r)).mp hN, k, ?_⟩
      have h : β ((ι r) ^ p ^ k) = 1 := by rw [map_pow, hk]
      exact β.injective (by rw [h, map_one])
    · rintro ⟨hN, k, hk⟩
      exact ⟨(hβN (ι r)).mpr hN, k, by rw [← map_pow, hk, map_one]⟩
  have hMfix : ∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ r ∈ Mb, kgInducedAut θ α r = r := by
    intro α hα hI r hr
    apply hι
    rw [(hh α hα hI).2.2.2 r]
    rw [hNab (h α) (hh α hα hI).1 (ι r) ((mem_Mb r).mp hr).1]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hM90 : ∀ c ∈ Mb, ((List.range p).map fun i => (kgInducedAut θ α₀ ^ i) c).prod = 1 →
      ∃ s ∈ Mb, c = s⁻¹ * kgInducedAut θ α₀ s := by
    intro c hc hcn
    have hnorm : ∀ i (x : R), ι ((kgInducedAut θ α₀ ^ i) x) = (β ^ i) (ι x) := by
      intro i
      induction i with
      | zero => intro x; simp
      | succ i ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, hβι, pow_succ, MulAut.mul_apply]
    have hcn' : ((List.range p).map fun i => (β ^ i) (ι c)).prod = 1 := by
      have hlist : (List.map ι ((List.range p).map fun i => (kgInducedAut θ α₀ ^ i) c))
          = List.map (fun i => (β ^ i) (ι c)) (List.range p) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hnorm i c
      have h := congrArg ι hcn
      rw [map_list_prod, map_one, hlist] at h
      exact h
    obtain ⟨s, hsN, hsp, hs⟩ := kgLangH90_pPart (c := ι c) hp β hNab hβN hH90
      ((mem_Mb c).mp hc).1 ((mem_Mb c).mp hc).2 hcn'
    obtain ⟨k, hk⟩ := hsp
    obtain ⟨s', hs'⟩ := hG1 s k hk
    refine ⟨s', ?_, ?_⟩
    · rw [mem_Mb]
      exact ⟨by rw [hs']; exact hsN, by rw [hs']; exact ⟨k, hk⟩⟩
    · apply hι
      rw [map_mul, map_inv, hs, hs', hβι, hs']
  obtain ⟨α, hαA, hαI, hαne⟩ := hne
  have hαN : h α ∈ N := (hh α hαA hαI).1
  have hαp : (h α) ^ p = 1 := (hh α hαA hαI).2.1
  have hαβ : β (h α) = h α := (hh α hαA hαI).2.2.1
  obtain ⟨eb, hebι⟩ := hG1 (h α) 1 (by rw [pow_one]; exact hαp)
  have heb : eb ∈ Mb := by
    rw [mem_Mb]
    exact ⟨by rw [hebι]; exact hαN, ⟨1, by rw [pow_one, hebι]; exact hαp⟩⟩
  have heb1 : eb ≠ 1 := by
    intro h1
    exact hαne (by rw [← hebι, h1, map_one])
  have hebp : eb ^ p = 1 := by
    apply hι
    rw [map_pow, map_one, hebι, hαp]
  have hebα : kgInducedAut θ α₀ eb = eb := by
    apply hι
    rw [hβι, hebι, hαβ]
  exact kgLangDescent hp θ hZ I A α₀ Mb hMab hMp hMst hMfix hM90 eb heb heb1 hebp hebα

private theorem kgLangModelAux_eq_one_of_centerQuotAut {K : Type*} [Group K]
    (hperf : commutator K = ⊤) (φ : MulAut K) (h : centerQuotAut K φ = 1) : φ = 1 := by
  have hmem : ∀ x : K, x⁻¹ * φ x ∈ Subgroup.center K := by
    intro x
    refine (QuotientGroup.eq_one_iff (x⁻¹ * φ x)).mp ?_
    have hx : (φ x : K ⧸ Subgroup.center K) = (x : K ⧸ Subgroup.center K) := by
      have h1 := DFunLike.congr_fun h (x : K ⧸ Subgroup.center K)
      rwa [centerQuotAut_mk, MulAut.one_apply] at h1
    calc ((x⁻¹ * φ x : K) : K ⧸ Subgroup.center K)
        = (x : K ⧸ Subgroup.center K)⁻¹ * (φ x : K ⧸ Subgroup.center K) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = (x : K ⧸ Subgroup.center K)⁻¹ * (x : K ⧸ Subgroup.center K) := by rw [hx]
      _ = 1 := inv_mul_cancel _
  let ψ : K →* Subgroup.center K :=
    { toFun := fun x => ⟨x⁻¹ * φ x, hmem x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x * y)⁻¹ * φ (x * y) = (x⁻¹ * φ x) * (y⁻¹ * φ y)
        rw [map_mul, mul_inv_rev]
        have hc : y⁻¹ * (x⁻¹ * φ x) = (x⁻¹ * φ x) * y⁻¹ :=
          Subgroup.mem_center_iff.mp (hmem x) y⁻¹
        rw [show y⁻¹ * x⁻¹ * (φ x * φ y) = y⁻¹ * (x⁻¹ * φ x) * φ y by group, hc]
        group }
  have hker : ψ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' (ψ a) (ψ b))
  ext x
  have hx1 : ψ x = 1 := by
    have : x ∈ ψ.ker := by rw [hker]; trivial
    simpa [MonoidHom.mem_ker] using this
  have hx2 : x⁻¹ * φ x = 1 := by
    change ((ψ x : Subgroup.center K) : K) = 1
    rw [hx1]
    rfl
  exact (inv_mul_eq_one.mp hx2).symm

theorem kgLangModelHom {p : ℕ} {K R G : Type} [Group K] [Group R] [Group G]
    (θ : K ⧸ Subgroup.center K ≃* R) (hperf : commutator K = ⊤)
    (ι : R →* G) (hι : Function.Injective ι)
    (hG5 : ∀ g : G, (∀ r, g * ι r = ι r * g) → g = 1)
    (J : Subgroup (MulAut R)) (hG6 : ∀ u ∈ J, ∃ h : G, ∀ r, ι (u r) = h * ι r * h⁻¹)
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A) (α₀ : MulAut K) (hα₀ : α₀ ∈ A)
    (β : MulAut G) (hβι : ∀ r, ι (kgInducedAut θ α₀ r) = β (ι r)) :
    ∃ h : MulAut K → G,
      (∀ α ∈ A, kgInducedAut θ α ∈ J → h α ^ p = 1 ∧ β (h α) = h α ∧
        ∀ r, ι (kgInducedAut θ α r) = h α * ι r * (h α)⁻¹) ∧
      (∀ α ∈ A, kgInducedAut θ α ∈ J → α ≠ 1 → h α ≠ 1) ∧
      (∀ α ∈ A, ∀ α' ∈ A, kgInducedAut θ α ∈ J → kgInducedAut θ α' ∈ J → h (α * α') = h α * h α') := by
  classical
  have huniq : ∀ (u : MulAut R) (h₁ h₂ : G),
      (∀ r, ι (u r) = h₁ * ι r * h₁⁻¹) → (∀ r, ι (u r) = h₂ * ι r * h₂⁻¹) → h₁ = h₂ := by
    intro u h₁ h₂ hh₁ hh₂
    have hcomm : ∀ r, (h₂⁻¹ * h₁) * ι r = ι r * (h₂⁻¹ * h₁) := by
      intro r
      have heq : h₁ * ι r * h₁⁻¹ = h₂ * ι r * h₂⁻¹ := by rw [← hh₁ r, ← hh₂ r]
      calc (h₂⁻¹ * h₁) * ι r
          = h₂⁻¹ * (h₁ * ι r * h₁⁻¹) * h₁ := by group
        _ = h₂⁻¹ * (h₂ * ι r * h₂⁻¹) * h₁ := by rw [heq]
        _ = ι r * (h₂⁻¹ * h₁) := by group
    exact (inv_mul_eq_one.mp (hG5 (h₂⁻¹ * h₁) hcomm)).symm
  have hinj : ∀ α : MulAut K, kgInducedAut θ α = 1 → α = 1 := by
    intro α hα
    have hcq : centerQuotAut K α = 1 := by
      have h1 : (MulAut.congr θ) (centerQuotAut K α) = 1 := by
        change (MulAut.congr θ).toMonoidHom (centerQuotAut K α) = 1
        simpa only [kgInducedAut, MonoidHom.comp_apply] using hα
      exact (MulAut.congr θ).injective (by rw [h1, map_one])
    exact kgLangModelAux_eq_one_of_centerQuotAut hperf α hcq
  let h : MulAut K → G := fun α =>
    if hJ : kgInducedAut θ α ∈ J then Classical.choose (hG6 (kgInducedAut θ α) hJ) else 1
  have hspec : ∀ (α : MulAut K) (hJ : kgInducedAut θ α ∈ J),
      ∀ r, ι (kgInducedAut θ α r) = h α * ι r * (h α)⁻¹ := by
    intro α hJ r
    have hαeq : h α = Classical.choose (hG6 (kgInducedAut θ α) hJ) := by
      simp only [h]; rw [dif_pos hJ]
    rw [hαeq]
    exact Classical.choose_spec (hG6 (kgInducedAut θ α) hJ) r
  refine ⟨h, ?_, ?_, ?_⟩
  · intro α hα hJ
    refine ⟨?_, ?_, hspec α hJ⟩
    · have hconj : ∀ n : ℕ, ∀ r : R,
          (h α) ^ n * ι r * ((h α) ^ n)⁻¹ = ι ((kgInducedAut θ α ^ n) r) := by
        intro n
        induction n with
        | zero => intro r; simp
        | succ n ih =>
          intro r
          rw [pow_succ, mul_inv_rev,
            show (h α) ^ n * h α * ι r * ((h α)⁻¹ * ((h α) ^ n)⁻¹)
                = (h α) ^ n * (h α * ι r * (h α)⁻¹) * ((h α) ^ n)⁻¹ by group,
            ← hspec α hJ r, ih (kgInducedAut θ α r), pow_succ, MulAut.mul_apply]
      apply hG5
      intro r
      have hp1 : (kgInducedAut θ α) ^ p = 1 := by
        rw [← map_pow, hA.2 α hα, map_one]
      have h1 := hconj p r
      rw [hp1, MulAut.one_apply] at h1
      have h3 : h α ^ p * ι r * (h α ^ p)⁻¹ * h α ^ p = ι r * h α ^ p := by rw [h1]
      rwa [mul_assoc (h α ^ p * ι r) ((h α ^ p)⁻¹) (h α ^ p), inv_mul_cancel, mul_one] at h3
    · have hg : (h α)⁻¹ * β (h α) = 1 := by
        apply hG5
        intro r
        obtain ⟨r', rfl⟩ := (kgInducedAut θ α₀).surjective r
        have hcommapply : (kgInducedAut θ α₀) ((kgInducedAut θ α) r')
            = (kgInducedAut θ α) ((kgInducedAut θ α₀) r') := by
          have hcommA : α₀ * α = α * α₀ := by
            letI : IsMulCommutative A := hA.1
            exact congrArg (fun x : A => (x : MulAut K))
              (mul_comm' (⟨α₀, hα₀⟩ : A) (⟨α, hα⟩ : A))
          rw [← MulAut.mul_apply, ← map_mul, hcommA, map_mul, MulAut.mul_apply]
        calc ((h α)⁻¹ * β (h α)) * ι ((kgInducedAut θ α₀) r')
            = (h α)⁻¹ * β (h α) * β (ι r') := by rw [hβι]
          _ = (h α)⁻¹ * β (h α * ι r') := by rw [map_mul]; group
          _ = (h α)⁻¹ * β (ι ((kgInducedAut θ α) r') * h α) := by
                rw [show h α * ι r' = ι ((kgInducedAut θ α) r') * h α by
                  rw [hspec α hJ r']; group]
          _ = (h α)⁻¹ * (β (ι ((kgInducedAut θ α) r')) * β (h α)) := by rw [map_mul]
          _ = (h α)⁻¹ * (ι ((kgInducedAut θ α₀) ((kgInducedAut θ α) r')) * β (h α)) := by
                rw [hβι]
          _ = (h α)⁻¹ * (ι ((kgInducedAut θ α) ((kgInducedAut θ α₀) r')) * β (h α)) := by
                rw [hcommapply]
          _ = (h α)⁻¹ * (h α * ι ((kgInducedAut θ α₀) r') * (h α)⁻¹ * β (h α)) := by
                rw [hspec α hJ]
          _ = ι ((kgInducedAut θ α₀) r') * ((h α)⁻¹ * β (h α)) := by group
      exact (inv_mul_eq_one.mp hg).symm
  · intro α hα hJ hαne hh
    apply hαne
    apply hinj
    ext r
    apply hι
    have h1 := hspec α hJ r
    rw [hh] at h1
    simpa using h1
  · intro α hα α' hα' hJ hJ'
    apply huniq (kgInducedAut θ (α * α')) (h (α * α')) (h α * h α')
    · exact hspec (α * α') (by rw [map_mul]; exact J.mul_mem hJ hJ')
    · intro r
      rw [map_mul, MulAut.mul_apply]
      calc ι (kgInducedAut θ α (kgInducedAut θ α' r))
          = h α * ι (kgInducedAut θ α' r) * (h α)⁻¹ := hspec α hJ _
        _ = h α * (h α' * ι r * (h α')⁻¹) * (h α)⁻¹ := by rw [hspec α' hJ' r]
        _ = (h α * h α') * ι r * (h α * h α')⁻¹ := by group

end CFSG.StandardType
