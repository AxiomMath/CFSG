module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWFrobAux
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48TailFrob

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_mem_commutator_of_automizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    (hcyc : ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁)
    (h1 : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (Bs : Set G))
    (hW : GGL48AutomizerMetaAt p Bs x)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hUR : U ≤ R) (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁)
    (hhom : ¬ GGL48Homocyclic p U₁)
    (hidx : (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)) = p)
    (hnn : ¬ ((ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
      (Subgroup.normalizer (U₁ : Set G))).Normal) :
    x ∉ ⁅Subgroup.normalizer (U₁ : Set G), Subgroup.normalizer (U₁ : Set G)⁆ := by
  obtain ⟨hp, hxp, hxN, ⟨e, he⟩, hpel⟩ := ggL48_facts hS h46 hRp hRmax hA
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hab, ⟨s, hs2, hexp, ⟨u₀, hu₀, hord⟩, ⟨x', hx'x, hx'⟩, Hh, r, hHU, -, hHcard, hHB,
    hB₁card⟩, -, hB₁iff, -, -⟩ := id h46
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set Z : Subgroup G := ggPowSubgroup U₁ hab (p ^ (s - 1)) with hZ
  set H₀ := ggL48H0 x U₁ with hH₀
  set C₀ : Subgroup G := Subgroup.centralizer (U₁ : Set G) with hC₀
  set N₀ : Subgroup G := Subgroup.normalizer (U₁ : Set G) with hN₀
  set D₀ : Subgroup G := H₀ ⊓ Subgroup.centralizer (B₁ : Set G) with hD₀
  set T : Subgroup G := C₀ ⊔ Subgroup.zpowers x' with hT
  set Kc : Subgroup G := H₀ ⊔ C₀ with hKc
  set CB : Subgroup G := Subgroup.centralizer (Bs : Set G) with hCB
  set Hn : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G)
    with hHn
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
  have hHN : H₀ ≤ N₀ := inf_le_right
  have hNB : N₀ ≤ Subgroup.normalizer (B₁ : Set G) := normalizer_le_normalizer_of_mem_iff hB₁iff
  have hU₁B : ∀ u ∈ B₁, u ∈ U₁ := fun u hu => ((hB₁iff u).mp hu).1
  have hcommB : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := fun a ha b hb =>
    hcomm a (hU₁B a ha) b (hU₁B b hb)
  have hNZ : ∀ n ∈ N₀, ∀ w ∈ Z, n * w * n⁻¹ ∈ Z := by
    intro n hn w hw
    obtain ⟨v, hv, rfl⟩ := mem_ggPowSubgroup.mp hw
    exact mem_ggPowSubgroup.mpr ⟨n * v * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn v).mp hv, conj_pow⟩
  obtain ⟨χ, hχ⟩ := GGL48TW.Frob.exists_units_hom (N := N₀) hordb hinf hdec hb₁B hZB hcommB
    (fun n hn u hu => (Subgroup.mem_normalizer_iff.mp (hNB hn) u).mp hu) hNZ
  set W' : Subgroup G := χ.ker.map N₀.subtype with hW'
  have hW'mem : ∀ g (hg : g ∈ N₀), g ∈ W' ↔ χ ⟨g, hg⟩ = 1 := by
    intro g hg
    constructor
    · intro hgW
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hgW
      have e' : (⟨g, hg⟩ : N₀) = n := Subtype.ext hng.symm
      rw [e']
      exact hn
    · intro h
      exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, h, rfl⟩
  have hW'N : W' ≤ N₀ := fun g hg => by
    obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact n.2
  have hW'act : ∀ g ∈ W', ∀ u ∈ B₁, ∃ w ∈ Z, g * u * g⁻¹ = u * w := by
    intro g hg
    exact (hχ ⟨g, hW'N hg⟩).mp ((hW'mem g (hW'N hg)).mp hg)
  have hW'cent : ∀ g ∈ N₀, g ∈ Subgroup.centralizer (B₁ : Set G) → g ∈ W' := by
    intro g hg hgc
    refine (hW'mem g hg).mpr ((hχ ⟨g, hg⟩).mpr fun u hu => ⟨1, Z.one_mem, ?_⟩)
    have := Subgroup.mem_centralizer_iff.mp hgc u hu
    show g * u * g⁻¹ = u * 1
    rw [← this]
    group
  have hpcop1 : Nat.Coprime p (p - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos one_pos))
  have hW'p : ∀ g ∈ N₀, ∀ k : ℕ, g ^ p ^ k = 1 → g ∈ W' := by
    intro g hg k hk
    refine (hW'mem g hg).mpr ?_
    have h1' : χ ⟨g, hg⟩ ^ p ^ k = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : N₀) ^ p ^ k = 1 := Subtype.ext (by simp [hk])
      rw [this, map_one]
    have h2 := orderOf_dvd_of_pow_eq_one h1'
    have h3 := ZMod.orderOf_units_dvd_card_sub_one (χ ⟨g, hg⟩)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k hpcop1)) h3)
  have hW'conj : ∀ n ∈ N₀, ∀ w ∈ W', n * w * n⁻¹ ∈ W' := by
    intro n hn w hw
    have hnw : n * w * n⁻¹ ∈ N₀ := N₀.mul_mem (N₀.mul_mem hn (hW'N hw)) (N₀.inv_mem hn)
    refine (hW'mem _ hnw).mpr ?_
    have e' : (⟨n * w * n⁻¹, hnw⟩ : N₀) = ⟨n, hn⟩ * ⟨w, hW'N hw⟩ * ⟨n, hn⟩⁻¹ := rfl
    rw [e', map_mul, map_mul, (hW'mem w (hW'N hw)).mp hw, mul_one, map_inv, mul_inv_cancel]
  have hC₀W : C₀ ≤ W' := fun c hc =>
    hW'cent c (hCN hc) (Subgroup.centralizer_le (fun b hb => hU₁B b hb) hc)
  have hD₀W : D₀ ≤ W' := fun g hg => hW'cent g (hHN hg.1) hg.2
  have hTconj : ∀ n ∈ N₀, ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
    intro n hn
    have hle : T ≤ T.comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hNC hn) c).mp hc)
      · rw [Subgroup.mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hc := GGL48.conj_mul_inv_mem_centralizer hx' hn
        have e' : n * x' * n⁻¹ = (n * x' * n⁻¹ * x'⁻¹) * x' := by group
        rw [e']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers x'))
    intro t ht
    have h1' := hle ht
    rw [Subgroup.mem_comap] at h1'
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1'
  have hTK : T ≤ Kc := sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hx'H))
  have hHC : H₀ ≤ Subgroup.normalizer (C₀ : Set G) := hHN.trans hNC
  have hKdec : ∀ k ∈ Kc, ∃ h ∈ H₀, ∃ c ∈ C₀, k = h * c := by
    intro k hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHC] at hk
    obtain ⟨h, hh, c, hc, hhc⟩ := hk
    exact ⟨h, hh, c, hc, hhc.symm⟩
  have hKN : Kc ≤ N₀ := sup_le hHN hCN
  have hC1 : ∀ m ∈ N₀, ∀ t ∈ T, t * (m⁻¹ * x' * m) * t⁻¹ = x' → m ∈ Kc := by
    intro m hm t ht hmt
    have hq : (m * t⁻¹) * x' * (m * t⁻¹)⁻¹ = x' := by
      calc (m * t⁻¹) * x' * (m * t⁻¹)⁻¹
          = (m * t⁻¹) * (t * (m⁻¹ * x' * m) * t⁻¹) * (m * t⁻¹)⁻¹ := by rw [hmt]
        _ = x' := by group
    have hqH : m * t⁻¹ ∈ H₀ := ⟨hcx _ hq, N₀.mul_mem hm (N₀.inv_mem (hTN ht))⟩
    have e' : m = (m * t⁻¹) * t := by group
    rw [e']
    exact Kc.mul_mem (Subgroup.mem_sup_left hqH) (hTK ht)
  have hZconj : ∀ u ∈ U₁, ∀ w ∈ Z, ∃ v ∈ U₁, x' * (u * w) = v * (x' * u) * v⁻¹ := by
    intro u hu w hw
    obtain ⟨v, hv, rfl⟩ := mem_ggPowSubgroup.mp hw
    refine ⟨v, hv, ?_⟩
    have hx'v : x'⁻¹ * v * x' = v * v ^ p ^ (s - 1) := by rw [hx' _ hv, pow_add, pow_one]
    have hvv : v * v ^ p ^ (s - 1) = v ^ p ^ (s - 1) * v := (Commute.self_pow v _).eq
    have hcu : (v * v ^ p ^ (s - 1)) * u = u * (v ^ p ^ (s - 1) * v) := by
      rw [← hvv]
      exact hcomm _ (U₁.mul_mem hv (U₁.pow_mem hv _)) _ hu
    symm
    calc v * (x' * u) * v⁻¹ = x' * (x'⁻¹ * v * x') * u * v⁻¹ := by group
      _ = x' * ((v * v ^ p ^ (s - 1)) * u) * v⁻¹ := by rw [hx'v]; group
      _ = x' * (u * (v ^ p ^ (s - 1) * v)) * v⁻¹ := by rw [hcu]
      _ = x' * (u * v ^ p ^ (s - 1)) := by group
  have hcore : ∀ k ∈ Kc ⊓ W', ∀ n ∈ N₀, n * k * n⁻¹ ∈ Kc := by
    rintro k ⟨hkK, hkW⟩ n hn
    have hkN : k ∈ N₀ := hKN hkK
    obtain ⟨g, hgT, u, hu, hup, hgu⟩ := exists_conj_eq_mul_of_mem_normalizer hS h46 hRp hRmax hA
      hs2 hexp hu₀ hord hx'x hx' hn
    have huB : u ∈ B₁ := (hB₁iff u).mpr ⟨hu, hup⟩
    obtain ⟨w, hw, hkw⟩ := hW'act k⁻¹ (W'.inv_mem hkW) u huB
    rw [inv_inv] at hkw
    obtain ⟨h, hh, c, hc, hkhc⟩ := hKdec k hkK
    have hhx' : h⁻¹ * x' * h = x' := by
      have hc' : Commute h x' := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
        rw [← hj]
        exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hh.1) j
      calc h⁻¹ * x' * h = h⁻¹ * (x' * h) := by group
        _ = h⁻¹ * (h * x') := by rw [hc'.eq]
        _ = x' := by group
    have e1 : k⁻¹ * x' * k = c⁻¹ * x' * c := by
      rw [hkhc]
      calc (h * c)⁻¹ * x' * (h * c) = c⁻¹ * (h⁻¹ * x' * h) * c := by group
        _ = c⁻¹ * x' * c := by rw [hhx']
    have hwU : w ∈ U₁ := hZU hw
    obtain ⟨v, hv, hve⟩ := hZconj u hu w hw
    have hcuw : c * (u * w) = (u * w) * c :=
      (Subgroup.mem_centralizer_iff.mp hc (u * w) (U₁.mul_mem hu hwU)).symm
    have hy : n⁻¹ * x' * n = g⁻¹ * (x' * u) * g := by rw [← hgu]; group
    have hky : k⁻¹ * (n⁻¹ * x' * n) * k =
        ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * (n⁻¹ * x' * n) * ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g)⁻¹ := by
      calc k⁻¹ * (n⁻¹ * x' * n) * k
          = (k⁻¹ * g⁻¹ * k) * (k⁻¹ * x' * k) * (k⁻¹ * u * k) * (k⁻¹ * g⁻¹ * k)⁻¹ := by
            rw [hy]; group
        _ = (k⁻¹ * g⁻¹ * k) * (c⁻¹ * x' * c) * (u * w) * (k⁻¹ * g⁻¹ * k)⁻¹ := by rw [e1, hkw]
        _ = (k⁻¹ * g⁻¹ * k) * c⁻¹ * x' * (c * (u * w)) * (k⁻¹ * g⁻¹ * k)⁻¹ := by group
        _ = (k⁻¹ * g⁻¹ * k) * c⁻¹ * x' * ((u * w) * c) * (k⁻¹ * g⁻¹ * k)⁻¹ := by rw [hcuw]
        _ = (k⁻¹ * g⁻¹ * k) * c⁻¹ * (x' * (u * w)) * c * (k⁻¹ * g⁻¹ * k)⁻¹ := by group
        _ = (k⁻¹ * g⁻¹ * k) * c⁻¹ * (v * (x' * u) * v⁻¹) * c * (k⁻¹ * g⁻¹ * k)⁻¹ := by rw [hve]
        _ = (k⁻¹ * g⁻¹ * k) * c⁻¹ * (v * (g * (n⁻¹ * x' * n) * g⁻¹) * v⁻¹) * c *
              (k⁻¹ * g⁻¹ * k)⁻¹ := by rw [hgu]
        _ = ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * (n⁻¹ * x' * n) *
              ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g)⁻¹ := by group
    have hg₁T : k⁻¹ * g⁻¹ * k ∈ T := by
      have := hTconj k⁻¹ (N₀.inv_mem hkN) g⁻¹ (T.inv_mem hgT)
      rwa [inv_inv] at this
    have ht₀T : (k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem hg₁T (Subgroup.mem_sup_left (C₀.inv_mem hc)))
        (Subgroup.mem_sup_left (hU₁C hv))) hgT
    have hm : n * k * n⁻¹ ∈ N₀ := N₀.mul_mem (N₀.mul_mem hn hkN) (N₀.inv_mem hn)
    refine hC1 (n * k * n⁻¹) hm (n * ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * n⁻¹)⁻¹
      (T.inv_mem (hTconj n hn _ ht₀T)) ?_
    calc (n * ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * n⁻¹)⁻¹ *
          ((n * k * n⁻¹)⁻¹ * x' * (n * k * n⁻¹)) *
          (n * ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * n⁻¹)⁻¹⁻¹
        = n * ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g)⁻¹ * (k⁻¹ * (n⁻¹ * x' * n) * k) *
            ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * n⁻¹ := by group
      _ = n * ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g)⁻¹ *
            (((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * (n⁻¹ * x' * n) *
              ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g)⁻¹) *
            ((k⁻¹ * g⁻¹ * k) * c⁻¹ * v * g) * n⁻¹ := by rw [hky]
      _ = x' := by group
  set N₁ : Subgroup G := Kc ⊓ W' with hN₁
  have hN₁N : N₁ ≤ N₀ := inf_le_left.trans hKN
  have hN₁conj : ∀ n ∈ N₀, ∀ k ∈ N₁, n * k * n⁻¹ ∈ N₁ := fun n hn k hk =>
    ⟨hcore k hk n hn, hW'conj n hn k hk.2⟩
  have hC₀N₁ : C₀ ≤ N₁ := le_inf le_sup_right hC₀W
  have hD₀N₁ : D₀ ≤ N₁ := le_inf (fun g hg => Subgroup.mem_sup_left hg.1) hD₀W
  set Sg : Set G := (C₀ : Set G) ∪ {g | g ∈ N₁ ∧ (orderOf g).Coprime p} with hSg
  set Y : Subgroup G := Subgroup.closure Sg with hY
  have hSconj : ∀ n ∈ N₀, ∀ g ∈ Sg, n * g * n⁻¹ ∈ Sg := by
    intro n hn g hg
    rcases hg with hg | ⟨hg, hgo⟩
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hNC hn) g).mp hg)
    · exact Or.inr ⟨hN₁conj n hn g hg, by rw [GGL48TW.Frob.orderOf_conj']; exact hgo⟩
  have hYN : N₀ ≤ Subgroup.normalizer (Y : Set G) := GGL48TW.Frob.le_normalizer_closure hSconj
  have hC₀Y : C₀ ≤ Y := fun c hc => Subgroup.subset_closure (Or.inl hc)
  have hYN₁ : Y ≤ N₁ := (Subgroup.closure_le _).mpr fun g hg => by
    rcases hg with hg | ⟨hg, -⟩
    · exact hC₀N₁ hg
    · exact hg
  have hYW : Y ≤ W' := hYN₁.trans inf_le_right
  have hpY : ∀ g ∈ N₁, ∃ k : ℕ, g ^ p ^ k ∈ Y := by
    intro g hg
    obtain ⟨a, m, hm, hord'⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.one_lt.ne'
    refine ⟨a, Subgroup.subset_closure (Or.inr ⟨N₁.pow_mem hg _, ?_⟩)⟩
    have hdvd : orderOf (g ^ p ^ a) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, ← hord', pow_orderOf_eq_one]
    exact Nat.Coprime.coprime_dvd_left hdvd ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  have hxH : x ∈ H₀ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxN⟩
  have hU₂n : H₀ ≤ Subgroup.normalizer (ggL48U2 x U₁ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, Subgroup.le_normalizer hg.1⟩
  have hxn := GGL48.not_mem_sup_inf_of_not_mem_sup hU₂n hHC
    (fun c hc k hck => ⟨hpel c hc.2 k hck, hc.1.1⟩) hxH hxp hcent
  have hxV : x ∉ ⁅H₀, H₀⁆ ⊔ C₀ := GGL48.not_mem_sup_of_not_mem_sup_inf hHC hxH hxn
  have hVK : ⁅H₀, H₀⁆ ⊔ C₀ ≤ Kc :=
    sup_le ((Subgroup.commutator_le_self H₀).trans le_sup_left) le_sup_right
  have hKV : Kc ≤ Subgroup.normalizer ((⁅H₀, H₀⁆ ⊔ C₀ : Subgroup G) : Set G) :=
    sup_le (fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨GGL48.le_normalizer_commutator H₀ hg, hHC hg⟩)
      (GGL48TW.Frob.le_normalizer_of_le hNC le_sup_right (hVK.trans hKN))
  have hxY : x ∉ Y :=
    GGL48TW.Frob.not_mem_closure_of_coprime hKV (GGL48.commutator_sup_le_sup hHC)
    (fun g hg => by
      rcases hg with hg | ⟨hg, hgo⟩
      · exact ⟨Subgroup.mem_sup_right hg, 1, Nat.coprime_one_left p,
          by rw [pow_one]; exact Subgroup.mem_sup_right hg⟩
      · exact ⟨hg.1, orderOf g, hgo, by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _⟩)
    hxp hxV
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  have hBseq : Bs = B₁ ⊔ Subgroup.zpowers x := hS.2.2.1.2
  have hB₁Bs : (B₁ : Set G) ⊆ Bs := fun b hb => hb.1
  have hH₀Hn : H₀ ≤ Hn := by
    intro g hg
    refine ⟨hg.1, ?_⟩
    have hgx : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_left (show Commute x g from
        (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm) j).eq
    have := Subgroup.inf_normalizer_le_normalizer_sup B₁ (Subgroup.zpowers x) ⟨hNB (hHN hg), hgx⟩
    rwa [← hBseq] at this
  have hCBx : CB ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxBs)
  have hCBHn : CB ≤ Hn := le_inf hCBx (Subgroup.centralizer_le_normalizer _)
  have hHnCB : Hn ≤ Subgroup.normalizer (CB : Set G) :=
    inf_le_right.trans (ggNormalizer_le_normalizer_centralizer Bs)
  have hCBB₁ : CB ≤ Subgroup.centralizer (B₁ : Set G) := Subgroup.centralizer_le hB₁Bs
  obtain ⟨h, hhH, hhcop, hH₀gen⟩ := GGL48TW.Frob.exists_coprime_generator hHN χ
  set E : Subgroup G := (H₀ ⊓ W') ⊔ CB with hE
  set M : Subgroup G := ((Y ⊓ H₀) ⊔ D₀) ⊔ CB with hM
  have hEH : E ≤ Hn := sup_le (inf_le_left.trans hH₀Hn) hCBHn
  have hM0H : (Y ⊓ H₀) ⊔ D₀ ≤ H₀ := sup_le inf_le_right inf_le_left
  have hMH : M ≤ Hn := sup_le (hM0H.trans hH₀Hn) hCBHn
  have hME : M ≤ E := sup_le ((sup_le (le_inf inf_le_right (inf_le_left.trans hYW))
    (le_inf inf_le_left hD₀W)).trans le_sup_left) le_sup_right
  have hCM : Hn ⊓ CB ≤ M := inf_le_right.trans le_sup_right
  have hH₀M : H₀ ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hYN (hHN hg), Subgroup.le_normalizer hg⟩,
          Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
            ggNormalizer_le_normalizer_centralizer B₁ (hNB (hHN hg))⟩⟩,
        hHnCB (hH₀Hn hg)⟩
  have hHnM : Hn ≤ Subgroup.normalizer (M : Set G) :=
    h1.trans (sup_le hH₀M (GGL48TW.Frob.le_normalizer_of_le hHnCB le_sup_right hMH))
  have hH₀E : H₀ ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    have hgW : g ∈ Subgroup.normalizer (W' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun hw => hW'conj g (hHN hg) w hw, fun hw => ?_⟩
      have := hW'conj g⁻¹ (N₀.inv_mem (hHN hg)) _ hw
      rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at this
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hgW⟩,
        hHnCB (hH₀Hn hg)⟩
  have hHnE : Hn ≤ Subgroup.normalizer (E : Set G) :=
    h1.trans (sup_le hH₀E (GGL48TW.Frob.le_normalizer_of_le hHnCB le_sup_right hEH))
  have hexpE : ∀ e ∈ E, ∃ k : ℕ, e ^ p ^ k ∈ M := by
    intro e he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_left.trans (hH₀Hn.trans hHnCB))] at he
    obtain ⟨a, ha, c, hc, rfl⟩ := he
    have ha' : a ∈ H₀ ⊓ W' := ha
    obtain ⟨k, hk⟩ := hpY a ⟨Subgroup.mem_sup_left ha'.1, ha'.2⟩
    refine ⟨k, ?_⟩
    have h2 := GGL48TW.Frob.mul_pow_mul_inv_pow_mem (hHnCB (hH₀Hn ha'.1)) hc (p ^ k)
    have e' : (a * c) ^ p ^ k = ((a * c) ^ p ^ k * (a ^ p ^ k)⁻¹) * a ^ p ^ k := by group
    rw [e']
    exact M.mul_mem (Subgroup.mem_sup_right h2)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨hk, H₀.pow_mem ha'.1 _⟩))
  have hhHn : h ∈ Hn := hH₀Hn hhH
  have hHnEh : Hn ≤ E ⊔ Subgroup.zpowers h :=
    h1.trans (sup_le (hH₀gen.trans (sup_le_sup_right le_sup_left _))
      (le_sup_right.trans le_sup_left))
  have hEM := hW M E h hME hEH hCM hHnM hHnE hexpE hhHn hhcop hHnEh
  have hN₁DY : N₁ ≤ D₀ ⊔ Y := by
    rintro k ⟨hkK, hkW⟩
    obtain ⟨h', hh', c, hc, hk⟩ := hKdec k hkK
    rw [hk] at hkW ⊢
    have hh'W : h' ∈ W' := by
      have e' : h' = (h' * c) * c⁻¹ := by group
      rw [e']
      exact W'.mul_mem hkW (W'.inv_mem (hC₀W hc))
    have hh'M : h' ∈ M := hEM (Subgroup.mem_sup_left ⟨hh', hh'W⟩)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((hM0H.trans hH₀Hn).trans hHnCB)] at hh'M
    obtain ⟨a, ha, c', hc', hac⟩ := hh'M
    have haH : a ∈ H₀ := hM0H ha
    have hc'H : c' ∈ H₀ := by
      have e' : c' = a⁻¹ * h' := by rw [← hac]; group
      rw [e']
      exact H₀.mul_mem (H₀.inv_mem haH) hh'
    have hc'D : c' ∈ D₀ := ⟨hc'H, hCBB₁ hc'⟩
    have hle : (Y ⊓ H₀) ⊔ D₀ ≤ D₀ ⊔ Y := sup_le (inf_le_left.trans le_sup_right) le_sup_left
    have haDY : a ∈ D₀ ⊔ Y := hle ha
    rw [← hac]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haDY (Subgroup.mem_sup_left hc'D))
      (Subgroup.mem_sup_right (hC₀Y hc))
  have hDN : D₀ ≤ N₀ := fun g hg => hHN hg.1
  have hcomm1 : ∀ n ∈ N₀, ∀ m ∈ N₁, ⁅n, m⁆ ∈ Y := by
    intro n hn m hm
    have hle : D₀ ⊔ Y ≤ GGL48.commModSubgroup Y n := sup_le
      (fun z hz => GGL48.mem_commModSubgroup.mpr ⟨hYN (hDN hz),
        hC₀Y (commutatorElement_mem_centralizer_of_frobenius hS h46 hRp hRmax hA hcyc hcent
          hidx hnn hn (Subgroup.mem_sup_left hz))⟩)
      (fun z hz => GGL48.mem_commModSubgroup.mpr ⟨hYN (hN₁N (hYN₁ hz)), by
        rw [commutatorElement_def]
        exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYN hn) z).mp hz) (Y.inv_mem hz)⟩)
    exact (GGL48.mem_commModSubgroup.mp (hle (hN₁DY hm))).2
  have hRN : R ≤ N₀ := Subgroup.le_normalizer.trans (normalizer_le_normalizer_of_forall_eq hA)
  have hU := hS.2.2.2.2.2.2.1
  have hxR : x ∈ R := hUR (hU.2.2.2 hxBs)
  have hpow : ∀ r ∈ R, ∃ k : ℕ, r ^ p ^ k = 1 := fun r hr => by
    obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hRK : Kc ⊓ R ≤ N₁ := fun r hr => ⟨hr.1, by
    obtain ⟨k, hk⟩ := hpow r hr.2
    exact hW'p r (hRN hr.2) k hk⟩
  have hR₁ind : (Kc ⊓ R).relIndex R ≤ p := by
    rw [Subgroup.inf_relIndex_right, ← hidx]
    exact Subgroup.relIndex_le_of_le_right hRN (by rw [hidx]; exact hp.ne_zero)
  obtain ⟨r₀, hr₀N, hRle⟩ : ∃ r₀ ∈ N₀, R ≤ Subgroup.zpowers r₀ ⊔ N₁ := by
    by_cases hRK' : R ≤ Kc
    · exact ⟨1, N₀.one_mem, fun r hr => Subgroup.mem_sup_right (hRK ⟨hRK' hr, hr⟩)⟩
    · obtain ⟨r₀, hr₀R, hr₀K⟩ := Set.not_subset.mp hRK'
      refine ⟨r₀, hRN hr₀R, ?_⟩
      have hM' : R ≤ Subgroup.zpowers r₀ ⊔ Kc ⊓ R :=
        GGL48.le_of_relIndex_le_prime le_sup_right
          (sup_le (Subgroup.zpowers_le.mpr hr₀R) inf_le_right) hRp hR₁ind
          (fun hle => hr₀K (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers r₀))).1)
      exact hM'.trans (sup_le_sup_left hRK _)
  have hRR : ⁅R, R⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have key : ∀ z ∈ N₀, ⁅z, r₀⁆ ∈ Y →
        Subgroup.zpowers r₀ ⊔ N₁ ≤ GGL48.commModSubgroup Y z := by
      intro z hz hzr
      exact sup_le (Subgroup.zpowers_le.mpr (GGL48.mem_commModSubgroup.mpr ⟨hYN hr₀N, hzr⟩))
        (fun m hm => GGL48.mem_commModSubgroup.mpr ⟨hYN (hN₁N hm), hcomm1 z hz m hm⟩)
    have har : a ∈ GGL48.commModSubgroup Y r₀ :=
      key r₀ hr₀N (by rw [commutatorElement_self]; exact Y.one_mem) (hRle ha)
    have h1' : ⁅a, r₀⁆ ∈ Y := by
      rw [← commutatorElement_inv]
      exact Y.inv_mem (GGL48.mem_commModSubgroup.mp har).2
    exact (GGL48.mem_commModSubgroup.mp (key a (hRN ha) h1' (hRle hb))).2
  have hindR : ¬ p ∣ (R ⊔ C₀).relIndex N₀ := by
    intro hdvd
    let S' : Sylow p G := ⟨R, hRp, fun {Q} hQ hRQ => hRmax Q hQ hRQ⟩
    have h1' : (R ⊔ C₀).relIndex N₀ ∣ R.relIndex N₀ :=
      Subgroup.relIndex_dvd_of_le_left N₀ le_sup_left
    have h2 : R.relIndex N₀ * N₀.index = R.index := Subgroup.relIndex_mul_index hRN
    have h3 : p ∣ R.index := h2 ▸ Dvd.dvd.mul_right (hdvd.trans h1') _
    exact S'.not_dvd_index h3
  exact GGL48.not_mem_commutator_of_not_dvd_relIndex hRN (Subgroup.centralizer_le_normalizer _)
    hNC hxR hxp (fun n hn => GGL48.conj_mul_inv_mem_centralizer he hn) hindR
    (fun hx => hxY ((sup_le hRR (inf_le_right.trans hC₀Y)) hx))

end CFSG.StandardType
