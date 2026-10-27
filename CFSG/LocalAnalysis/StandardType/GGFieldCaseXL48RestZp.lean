module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Rest
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Homocyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_mul_of_mem_normalizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) {s : ℕ} {x' : G} (hs2 : 2 ≤ s)
    (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1) {u₀ : G} (hu₀ : u₀ ∈ U₁) (hord : orderOf u₀ = p ^ s)
    (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hx' : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) {n : G}
    (hn : n ∈ Subgroup.normalizer (U₁ : Set G)) :
    ∃ g ∈ Subgroup.centralizer (U₁ : Set G) ⊔ Subgroup.zpowers x', ∃ u ∈ U₁, u ^ p = 1 ∧
      g * (n⁻¹ * x' * n) * g⁻¹ = x' * u := by
  obtain ⟨hp, hxp, hxN, -, hpel⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  have hab : IsMulCommutative U₁ := h46.1
  have hU₁p : IsPGroup p U₁ := hRp.to_le (mem_thompsonAbelianSubgroups_of_forall_eq hA).1
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  have hU₁C : U₁ ≤ C₀ := Subgroup.le_centralizer_iff_isMulCommutative.mpr hab
  have hCN : C₀ ≤ N₀ := Subgroup.centralizer_le_normalizer _
  have hNC : N₀ ≤ Subgroup.normalizer (C₀ : Set G) := ggNormalizer_le_normalizer_centralizer U₁
  have hx'mem : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
  have hx'p : x' ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hx'N : x' ∈ N₀ := (Subgroup.zpowers_le.mpr hxN) hx'mem
  have hzC : ∀ i : ℕ, x' ^ i ∈ C₀ → x' ^ i = 1 := by
    intro i hi
    by_cases hpi : p ∣ i
    · obtain ⟨c, rfl⟩ := hpi
      rw [pow_mul, hx'p, one_pow]
    · exfalso
      have h1 := pow_pow_sub_one_eq_one_of_commute hs2 hexp hx' hpi hu₀
        ((Subgroup.mem_centralizer_iff.mp hi) u₀ hu₀).symm
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      have h3 := Nat.le_of_dvd (pow_pos hp.pos _) h2
      have h4 : p ^ (s - 1) < p ^ s := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
  set z : G := n⁻¹ * x' * n with hz
  have hcn : n⁻¹ * x' * n⁻¹⁻¹ * x'⁻¹ ∈ C₀ :=
    GGL48.conj_mul_inv_mem_centralizer hx' (N₀.inv_mem hn)
  rw [inv_inv] at hcn
  have hzT : z ∈ C₀ ⊔ Subgroup.zpowers x' := by
    have e : z = (n⁻¹ * x' * n * x'⁻¹) * x' := by rw [hz]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcn)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x'))
  have hzp : z ^ p = 1 := by
    rw [hz, show n⁻¹ * x' * n = n⁻¹ * x' * n⁻¹⁻¹ by rw [inv_inv], conj_pow, hx'p]
    group
  obtain ⟨g, hgT, hgS⟩ := GGL48.exists_conj_mem_sup_of_pow_eq_one hU₁C
    (fun c hc k hk => hpel c hc k hk) hU₁p (hNC hx'N) hx'N hx'p hzT hzp
  have hTN : C₀ ⊔ Subgroup.zpowers x' ≤ N₀ := sup_le hCN (Subgroup.zpowers_le.mpr hx'N)
  have hgN : g ∈ N₀ := hTN hgT
  have hgS' : g * z * g⁻¹ ∈ ((Subgroup.zpowers x' ⊔ U₁ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hgS
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hx'N)] at hgS'
  obtain ⟨w, hw, u, hu, hwu⟩ := hgS'
  dsimp only at hwu
  replace hwu : g * z * g⁻¹ = w * u := hwu.symm
  have hm : (g * n⁻¹) * x' * (g * n⁻¹)⁻¹ * x'⁻¹ ∈ C₀ :=
    GGL48.conj_mul_inv_mem_centralizer hx' (N₀.mul_mem hgN (N₀.inv_mem hn))
  have hwx : w * x'⁻¹ ∈ C₀ := by
    have e : w * x'⁻¹ = ((g * n⁻¹) * x' * (g * n⁻¹)⁻¹ * x'⁻¹) * (x' * u⁻¹ * x'⁻¹) := by
      have h1 : (g * n⁻¹) * x' * (g * n⁻¹)⁻¹ = w * u := by rw [← hwu, hz]; group
      rw [h1]
      group
    have hconj : x' * u⁻¹ * x'⁻¹ ∈ C₀ :=
      hU₁C ((Subgroup.mem_normalizer_iff.mp hx'N _).mp (U₁.inv_mem hu))
    rw [e]
    exact C₀.mul_mem hm hconj
  have hw' : w = x' := by
    have hwz : w * x'⁻¹ ∈ Subgroup.zpowers x' :=
      Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (Subgroup.mem_zpowers x'))
    rw [← mem_powers_iff_mem_zpowers] at hwz
    obtain ⟨i, hi⟩ := hwz
    dsimp only at hi
    have := hzC i (by rw [hi]; exact hwx)
    rw [hi] at this
    calc w = w * x'⁻¹ * x' := by group
      _ = x' := by rw [this, one_mul]
  rw [hw'] at hwu
  have hupow : ∀ v ∈ U₁, v ^ (p ^ (s - 1) * p ^ (s - 1)) = 1 := by
    intro v hv
    have e : p ^ (s - 1) * p ^ (s - 1) = p ^ s * p ^ (s - 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, pow_mul, hexp v hv, one_pow]
  have hup : u ^ p = 1 := by
    set a : G := u ^ p ^ (s - 1) with ha
    have haU : a ∈ U₁ := U₁.pow_mem hu _
    have hxu : x'⁻¹ * u * x' = u * a := by rw [hx' u hu, pow_add, pow_one]
    have hxa : x'⁻¹ * a * x' = a := by
      rw [hx' a haU, pow_add, pow_one, ha, ← pow_mul, hupow u hu, mul_one]
    have hap : a ^ p = 1 := by
      rw [ha, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s), hexp u hu]
    have h1 := GGL48.mul_pow_prime_eq hp hp2 hxu hxa ((Commute.refl u).pow_right _) hx'p hap
    rw [← h1, ← hwu, conj_pow, hzp]
    group
  exact ⟨g, hgT, u, hu, hup, hwu⟩

theorem relIndex_le_of_not_homocyclic {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) (hhom : ¬ GGL48Homocyclic p U₁) :
    (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)) ≤ p := by
  obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hab, ⟨s, hs2, hexp, ⟨u₀, hu₀, hord⟩, ⟨x', hx'x, hx'⟩, H, r, hHU, -, hHcard, hHB,
    hB₁card⟩, -, hB₁iff, -, -⟩ := id h46
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set Z : Subgroup G := ggPowSubgroup U₁ hab (p ^ (s - 1)) with hZ
  set H₀ := ggL48H0 x U₁ with hH₀
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set T : Subgroup G := C₀ ⊔ Subgroup.zpowers x' with hT
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hU₁C : U₁ ≤ C₀ := Subgroup.le_centralizer_iff_isMulCommutative.mpr hab
  have hCN : C₀ ≤ N₀ := Subgroup.centralizer_le_normalizer _
  have hNC : N₀ ≤ Subgroup.normalizer (C₀ : Set G) := ggNormalizer_le_normalizer_centralizer U₁
  have hx'mem : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
  have hxmem : x ∈ Subgroup.zpowers x' := hx'x.symm ▸ Subgroup.mem_zpowers x
  have hx'N : x' ∈ N₀ := (Subgroup.zpowers_le.mpr hxN) hx'mem
  have hTN : T ≤ N₀ := sup_le hCN (Subgroup.zpowers_le.mpr hx'N)
  have hcx : ∀ m : G, m * x' * m⁻¹ = x' → m ∈ Subgroup.centralizer ({x} : Set G) := by
    intro m hm
    have hc : Commute m x' := by
      show m * x' = x' * m
      calc m * x' = m * x' * m⁻¹ * m := by group
        _ = x' * m := by rw [hm]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc.zpow_right k).eq
  have hx'H : x' ∈ H₀ := ⟨hcx x' (by group), hx'N⟩
  have hBZ : Nat.card B₁ ≤ p * Nat.card Z :=
    card_le_mul_card_ggPowSubgroup hp (by omega) hab hB₁iff hHU hHcard hHB hB₁card
  have hns : ∃ b₁ ∈ U₁, b₁ ^ p = 1 ∧ ∀ v ∈ U₁, v ^ p ^ (s - 1) ≠ b₁ := by
    by_contra hcon
    push Not at hcon
    unfold GGL48Homocyclic at hhom
    apply hhom
    intro s' hs' hexp' hord' b hb hbp
    have hss : s' = s := by
      obtain ⟨u', hu', hord'⟩ := hord'
      have h1 : p ^ s ∣ p ^ s' := hord ▸ orderOf_dvd_of_pow_eq_one (hexp' u₀ hu₀)
      have h2 : p ^ s' ∣ p ^ s := hord' ▸ orderOf_dvd_of_pow_eq_one (hexp u' hu')
      have h3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
      have h4 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
      omega
    rw [hss]
    exact hcon b hb hbp
  obtain ⟨b₁, hb₁U, hb₁p, hb₁⟩ := hns
  have hZB : Z ≤ B₁ := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_ggPowSubgroup.mp hw
    refine (hB₁iff _).mpr ⟨U₁.pow_mem hv _, ?_⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s), hexp v hv]
  have hZU : Z ≤ U₁ := hZB.trans (fun u hu => ((hB₁iff u).mp hu).1)
  have hb₁B : b₁ ∈ B₁ := (hB₁iff b₁).mpr ⟨hb₁U, hb₁p⟩
  have hb₁Z : b₁ ∉ Z := fun hmem => by
    obtain ⟨v, hv, hvb⟩ := mem_ggPowSubgroup.mp hmem
    exact hb₁ v hv hvb
  have hb₁ne : b₁ ≠ 1 := fun h => hb₁Z (h ▸ Z.one_mem)
  have hordb : orderOf b₁ = p := orderOf_eq_prime hb₁p hb₁ne
  have hbN : Subgroup.zpowers b₁ ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hcomm _ (hZU hw) _ hb₁U
  have hinf : Subgroup.zpowers b₁ ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    rw [Subgroup.mem_bot]
    by_contra hw
    apply hb₁Z
    have hwp : w ^ p = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb₁p, one_zpow]
    have hordw : orderOf w = p := orderOf_eq_prime hwp hw
    have heq : Subgroup.zpowers w = Subgroup.zpowers b₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw1)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hordw, hordb])
    have hbw : b₁ ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers b₁
    exact (Subgroup.zpowers_le.mpr hw2) hbw
  have hEB : Subgroup.zpowers b₁ ⊔ Z = B₁ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hb₁B) hZB) ?_
    rw [card_sup_eq_mul_of_inf_eq_bot hbN hinf, Nat.card_zpowers, hordb]
    exact hBZ
  have hdec : ∀ u ∈ B₁, ∃ i < p, ∃ w ∈ Z, u = b₁ ^ i * w := by
    intro u hu
    rw [← hEB, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbN] at hu
    obtain ⟨a, ha, w, hw, rfl⟩ := hu
    rw [SetLike.mem_coe, ← mem_powers_iff_mem_zpowers] at ha
    obtain ⟨k, rfl⟩ := ha
    refine ⟨k % p, Nat.mod_lt _ hp.pos, w, hw, ?_⟩
    rw [← hordb, pow_mod_orderOf]
  have hinv : ∀ n ∈ N₀, ∃ i < p, ∃ g ∈ T, g * (n⁻¹ * x' * n) * g⁻¹ = x' * b₁ ^ i := by
    intro n hn
    obtain ⟨g, hgT, u, hu, hup, hgu⟩ := exists_conj_eq_mul_of_mem_normalizer hS h46 hRp hRmax hA
      hs2 hexp hu₀ hord hx'x hx' hn
    obtain ⟨i, hi, w, hw, rfl⟩ := hdec u ((hB₁iff u).mpr ⟨hu, hup⟩)
    obtain ⟨v, hv, rfl⟩ := mem_ggPowSubgroup.mp hw
    refine ⟨i, hi, v⁻¹ * g, T.mul_mem (Subgroup.mem_sup_left (hU₁C (U₁.inv_mem hv))) hgT, ?_⟩
    have hx'v : x'⁻¹ * v⁻¹ * x' = v⁻¹ * (v⁻¹) ^ p ^ (s - 1) := by
      rw [hx' _ (U₁.inv_mem hv), pow_add, pow_one]
    have h1 : b₁ ^ i * v ^ p ^ (s - 1) = v ^ p ^ (s - 1) * b₁ ^ i :=
      hcomm _ (U₁.pow_mem hb₁U _) _ (U₁.pow_mem hv _)
    have h2 : b₁ ^ i * v = v * b₁ ^ i := hcomm _ (U₁.pow_mem hb₁U _) _ hv
    calc (v⁻¹ * g) * (n⁻¹ * x' * n) * (v⁻¹ * g)⁻¹
        = v⁻¹ * (g * (n⁻¹ * x' * n) * g⁻¹) * v := by group
      _ = v⁻¹ * (x' * (b₁ ^ i * v ^ p ^ (s - 1))) * v := by rw [hgu]
      _ = x' * (x'⁻¹ * v⁻¹ * x') * (b₁ ^ i * v ^ p ^ (s - 1)) * v := by group
      _ = x' * (v⁻¹ * (v ^ p ^ (s - 1))⁻¹) * (v ^ p ^ (s - 1) * b₁ ^ i) * v := by
        rw [hx'v, inv_pow, h1]
      _ = x' * v⁻¹ * (b₁ ^ i * v) := by group
      _ = x' * b₁ ^ i := by rw [h2]; group
  have hTconj : ∀ n ∈ N₀, ∀ t ∈ T, n * t * n⁻¹ ∈ H₀ ⊔ C₀ := by
    intro n hn
    have hle : T ≤ (H₀ ⊔ C₀).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hNC hn) c).mp hc)
      · rw [Subgroup.mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hc := GGL48.conj_mul_inv_mem_centralizer hx' hn
        have e : n * x' * n⁻¹ = (n * x' * n⁻¹ * x'⁻¹) * x' := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx'H)
    intro t ht
    have h1 := hle ht
    rw [Subgroup.mem_comap] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have hsame : ∀ n ∈ N₀, ∀ m ∈ N₀, ∀ g ∈ T, ∀ g' ∈ T,
      g * (n⁻¹ * x' * n) * g⁻¹ = g' * (m⁻¹ * x' * m) * g'⁻¹ → m * n⁻¹ ∈ H₀ ⊔ C₀ := by
    intro n hn m hm g hg g' hg' heq
    set k : G := m * g'⁻¹ * g * n⁻¹ with hk
    have hkx : k * x' * k⁻¹ = x' := by
      have h1 : (g * n⁻¹) * x' * (g * n⁻¹)⁻¹ = (g' * m⁻¹) * x' * (g' * m⁻¹)⁻¹ := by
        calc (g * n⁻¹) * x' * (g * n⁻¹)⁻¹ = g * (n⁻¹ * x' * n) * g⁻¹ := by group
          _ = g' * (m⁻¹ * x' * m) * g'⁻¹ := heq
          _ = (g' * m⁻¹) * x' * (g' * m⁻¹)⁻¹ := by group
      calc k * x' * k⁻¹
          = (g' * m⁻¹)⁻¹ * ((g * n⁻¹) * x' * (g * n⁻¹)⁻¹) * (g' * m⁻¹) := by rw [hk]; group
        _ = (g' * m⁻¹)⁻¹ * ((g' * m⁻¹) * x' * (g' * m⁻¹)⁻¹) * (g' * m⁻¹) := by rw [h1]
        _ = x' := by group
    have hkN : k ∈ N₀ := N₀.mul_mem (N₀.mul_mem (N₀.mul_mem hm (N₀.inv_mem (hTN hg')))
      (hTN hg)) (N₀.inv_mem hn)
    have hkH : k ∈ H₀ := ⟨hcx k hkx, hkN⟩
    have e : m * n⁻¹ = k * (n * (g⁻¹ * g') * n⁻¹) := by rw [hk]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkH)
      (hTconj n hn _ (T.mul_mem (T.inv_mem hg) hg'))
  have hinv' : ∀ n : N₀, ∃ i < p, ∃ g ∈ T, g * ((n : G)⁻¹ * x' * n) * g⁻¹ = x' * b₁ ^ i :=
    fun n => hinv n n.2
  choose f hf using hinv'
  let F : N₀ ⧸ (H₀ ⊔ C₀).subgroupOf N₀ → Fin p := fun q => ⟨f q.out⁻¹, (hf q.out⁻¹).1⟩
  have hF : Function.Injective F := by
    intro q q' hqq
    have hfe : f q.out⁻¹ = f q'.out⁻¹ := congrArg Fin.val hqq
    obtain ⟨-, g, hg, hgeq⟩ := hf q.out⁻¹
    obtain ⟨-, g', hg', hgeq'⟩ := hf q'.out⁻¹
    rw [hfe] at hgeq
    have h1 := hsame _ (q.out⁻¹).2 _ (q'.out⁻¹).2 g hg g' hg' (hgeq.trans hgeq'.symm)
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h2 := (H₀ ⊔ C₀).inv_mem h1
    simpa [mul_inv_rev] using h2
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_fin] at hcard
  exact hcard

theorem exists_monoidHom_of_normal {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) (hhom : ¬ GGL48Homocyclic p U₁)
    (hind : p ∣ (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)))
    (hnorm : ((ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
      (Subgroup.normalizer (U₁ : Set G))).Normal) :
    ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1 := by
  obtain ⟨hp, -, -, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  set Kq := (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
    (Subgroup.normalizer (U₁ : Set G)) with hKq
  have hle := relIndex_le_of_not_homocyclic hS h46 hRp hRmax hA hhom
  have hpos : 0 < Kq.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  have hQ : Nat.card (Subgroup.normalizer (U₁ : Set G) ⧸ Kq) = p :=
    le_antisymm hle (Nat.le_of_dvd hpos hind)
  have hZp : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  let e := mulEquivOfPrimeCardEq hQ hZp
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' Kq), fun h => ?_⟩
  have hne : (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
    rw [Ne, ofAdd_eq_one]
    exact one_ne_zero
  obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd (1 : ZMod p))
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective Kq q
  apply hne
  rw [← hq]
  have h1 := congrArg (fun ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p) => ψ n) h
  simpa using h1

end Config

end CFSG.StandardType

end
