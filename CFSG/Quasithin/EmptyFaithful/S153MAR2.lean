module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace S153M

private theorem isNilpotentTwo_of_central_two_quot {Ω : Type*} [Group Ω] [Finite Ω]
    {N A : Subgroup Ω} (hc : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a)
    (h2 : ∀ n ∈ N, ∃ e : ℕ, n ^ 2 ^ e ∈ A) : Group.IsNilpotent ↥N := by
  have hAn : (A.subgroupOf N).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have h1 := hc a ha g g.2
    have e : (g : Ω) * a * (g : Ω)⁻¹ = a := by
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    show (g : Ω) * a * (g : Ω)⁻¹ ∈ A
    rw [e]
    exact ha
  have hcen : (QuotientGroup.mk' (A.subgroupOf N)).ker ≤ Subgroup.center ↥N := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subgroup.mem_subgroupOf] at ha
    exact Subtype.ext (hc a ha g g.2).symm
  have hP : IsPGroup 2 (↥N ⧸ A.subgroupOf N) := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 n n.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  have : Group.IsNilpotent (↥N ⧸ A.subgroupOf N) := hP.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (A.subgroupOf N)) hcen

private theorem perfectTwo_double_commutator {Ω : Type*} [Group Ω] {P X : Subgroup Ω}
    (hP : ⁅P, P⁆ = P) (h : ⁅⁅P, X⁆, P⁆ = ⊥) : ⁅P, X⁆ = ⊥ := by
  have h' : ⁅⁅X, P⁆, P⁆ = ⊥ := by rw [Subgroup.commutator_comm X P]; exact h
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h h'
  rwa [hP] at h3

private theorem le_normalizer_of_commuteTwo {Ω : Type*} [Group Ω] {K K' : Subgroup Ω}
    (hc : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) : K' ≤ Subgroup.normalizer (K : Set Ω) :=
  fun b hb => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb)

private theorem commuteTwo_of_normal_not_le {Ω : Type*} [Group Ω] {K K' M : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hc : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hN : (K ⊔ K').Normal) (hM : M.Normal) (hKM : ¬ K ≤ M) :
    ∀ m ∈ M, ∀ k ∈ K, m * k = k * m := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp ⟨hq.1⟩
  have hb : ∀ n ∈ M ⊓ K, ∀ l ∈ K, n * l = l * n :=
    B1Red.commute_of_normal_not_le hq
      (fun n hn l hl => K.mul_mem (K.mul_mem hn.2 hl) (K.inv_mem hn.2))
      (fun l hl n hn => ⟨hM.conj_mem n hn.1 l, K.mul_mem (K.mul_mem hl hn.2) (K.inv_mem hl)⟩)
      (fun h => hKM (fun k hk => (h hk).1))
  have hbc : M ⊓ K ≤ Subgroup.centralizer (K : Set Ω) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (hb x hx l hl).symm
  have hKn' : K' ≤ Subgroup.normalizer (K : Set Ω) := le_normalizer_of_commuteTwo hc
  have hcomm1 : ⁅K, M ⊓ (K ⊔ K')⁆ ≤ M ⊓ K := by
    rw [Subgroup.commutator_le]
    rintro g₁ hg₁ g₂ ⟨hg₂M, hg₂N⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hKn').1 hg₂N
    refine ⟨M.mul_mem (hM.conj_mem (x * y) hg₂M g₁) (M.inv_mem hg₂M), ?_⟩
    have hy' : y * g₁⁻¹ = g₁⁻¹ * y := (hc g₁⁻¹ (K.inv_mem hg₁) y hy).symm
    have e : g₁ * (x * y) * g₁⁻¹ * (x * y)⁻¹ = g₁ * x * g₁⁻¹ * x⁻¹ := by
      calc g₁ * (x * y) * g₁⁻¹ * (x * y)⁻¹ = g₁ * x * (y * g₁⁻¹) * y⁻¹ * x⁻¹ := by group
        _ = g₁ * x * (g₁⁻¹ * y) * y⁻¹ * x⁻¹ := by rw [hy']
        _ = g₁ * x * g₁⁻¹ * x⁻¹ := by group
    show g₁ * (x * y) * g₁⁻¹ * (x * y)⁻¹ ∈ K
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem hg₁ hx) (K.inv_mem hg₁)) (K.inv_mem hx)
  have hcomm2 : ⁅K, M ⊓ (K ⊔ K')⁆ = ⊥ := by
    refine perfectTwo_double_commutator hperf ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hcomm1.trans hbc
  have hcomm3 : ⁅K, M⁆ ≤ M ⊓ (K ⊔ K') := by
    rw [Subgroup.commutator_le]
    intro k hk m hm
    refine ⟨M.mul_mem (hM.conj_mem m hm k) (M.inv_mem hm), ?_⟩
    have h1 : m * k⁻¹ * m⁻¹ ∈ K ⊔ K' :=
      hN.conj_mem k⁻¹ ((K ⊔ K').inv_mem (Subgroup.mem_sup_left hk)) m
    have e : k * m * k⁻¹ * m⁻¹ = k * (m * k⁻¹ * m⁻¹) := by group
    show k * m * k⁻¹ * m⁻¹ ∈ K ⊔ K'
    rw [e]
    exact (K ⊔ K').mul_mem (Subgroup.mem_sup_left hk) h1
  have hcomm4 : ⁅K, M⁆ = ⊥ := by
    refine perfectTwo_double_commutator hperf ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    have hx' := hcomm3 hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h5 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm2 hl
    exact (Subgroup.mem_centralizer_iff.1 h5 x hx').symm
  intro m hm k hk
  have h3 : ⁅k, m⁆ ∈ (⊥ : Subgroup Ω) := hcomm4 ▸ Subgroup.commutator_mem_commutator hk hm
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

private theorem isQuasisimpleTwo_map {H : Type*} [Group H] {W : Type*} [Group W] (f : H →* W)
    (K : Subgroup H) (hq : CFSG.Open.IsQuasisimple ↥K) (hnt : ¬ K ≤ f.ker) :
    CFSG.Open.IsQuasisimple ↥(K.map f) := by
  have hrange : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : (f.comp K.subtype).ker ≠ ⊤ := by
    intro h
    apply hnt
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ (f.comp K.subtype).ker := by rw [h]; trivial
    exact this
  rw [← hrange]
  exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq _ hker

private theorem ar_coreTwo {H : Type} [Group H] [Finite H] {V : Type} [CommGroup V] [Finite V]
    (ρ : H →* MulAut V) (K₁ K₂ : Subgroup H)
    (hq₁ : CFSG.Open.IsQuasisimple ↥K₁) (hq₂ : CFSG.Open.IsQuasisimple ↥K₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hN : (K₁ ⊔ K₂).Normal)
    (hO2 : CFSG.pCore 2 H = ⊥) (h2 : ∀ y : H, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₂)
    (hnt₁ : ¬ K₁ ≤ ρ.ker) (hnt₂ : ¬ K₂ ≤ ρ.ker) :
    CFSG.Open.IsQuasisimple ↥(K₁.map ρ) ∧ CFSG.Open.IsQuasisimple ↥(K₂.map ρ) ∧
      pCoreOf 2 ρ.range = ⊥ := by
  have hL₁ := isQuasisimpleTwo_map ρ K₁ hq₁ hnt₁
  have hL₂ := isQuasisimpleTwo_map ρ K₂ hq₂ hnt₂
  refine ⟨hL₁, hL₂, ?_⟩
  set X := ρ.range with hX
  set R := pCoreOf 2 X with hR
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hRn : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx) r).mp hr
  set M : Subgroup H := R.comap ρ with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm h => ?_⟩
    have hm' : ρ m ∈ R := hm
    show ρ (h * m * h⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hRn (ρ h) ⟨h, rfl⟩ (ρ m) hm'
  have hKM : ∀ K : Subgroup H, CFSG.Open.IsQuasisimple ↥(K.map ρ) → ¬ K ≤ M := by
    intro K hL hKM
    have hLR : K.map ρ ≤ R := by
      rintro _ ⟨k, hk, rfl⟩
      exact hKM hk
    have hnil : Group.IsNilpotent ↥(K.map ρ) := (hR2.to_le hLR).isNilpotent
    have : Group.IsPerfect ↥(K.map ρ) := ⟨hL.1⟩
    have : Nontrivial ↥(K.map ρ) := CFSG.ComponentClassification.Quasisimple.nontrivial hL
    exact Group.IsPerfect.not_isNilpotent ↥(K.map ρ) hnil
  have hc₁ := commuteTwo_of_normal_not_le hq₁ hc hN hMn (hKM K₁ hL₁)
  have hc₂ := commuteTwo_of_normal_not_le hq₂ (fun a ha b hb => (hc b hb a ha).symm)
    (by rwa [sup_comm]) hMn (hKM K₂ hL₂)
  have hK₂n : K₂ ≤ Subgroup.normalizer (K₁ : Set H) := le_normalizer_of_commuteTwo hc
  set N : Subgroup H := K₁ ⊔ K₂ with hNdef
  set C : Subgroup H := Subgroup.centralizer (N : Set H) with hC
  have hMC : M ≤ C := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨x, hx, y, hy, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hK₂n).1 hn
    calc x * y * m = x * (y * m) := mul_assoc _ _ _
      _ = x * (m * y) := by rw [hc₂ m hm y hy]
      _ = x * m * y := (mul_assoc _ _ _).symm
      _ = m * x * y := by rw [hc₁ m hm x hx]
      _ = m * (x * y) := mul_assoc _ _ _
  have hCn : ∀ y ∈ (⊤ : Subgroup H), ∀ x ∈ C, y * x * y⁻¹ ∈ C := by
    intro y _ x hx
    refine Subgroup.mem_centralizer_iff.2 fun n hn => ?_
    have h1 : (y⁻¹ * n * y⁻¹⁻¹) ∈ N := hN.conj_mem n hn y⁻¹
    have h2' := Subgroup.mem_centralizer_iff.1 hx _ h1
    calc n * (y * x * y⁻¹) = y * ((y⁻¹ * n * y⁻¹⁻¹) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * n * y⁻¹⁻¹)) * y⁻¹ := by rw [h2']
      _ = y * x * y⁻¹ * n := by group
  have hCnil : Group.IsNilpotent ↥C :=
    isNilpotentTwo_of_central_two_quot (A := N ⊓ C)
      (fun a ha n hn => Subgroup.mem_centralizer_iff.1 hn a ha.1)
      (fun n hn => by
        obtain ⟨e, he⟩ := h2 n
        exact ⟨e, he, C.pow_mem hn _⟩)
  have hO2' : pCoreOf 2 (⊤ : Subgroup H) = ⊥ := by
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (⊤ : Subgroup H)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
    have hPn : (pCoreOf 2 (⊤ : Subgroup H)).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤)
    have : pCoreOf 2 (⊤ : Subgroup H) ≤ CFSG.pCore 2 H := le_sSup ⟨hPn, hP2⟩
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hodd := B1Red.odd_orderOf_of_nilpotent_normal (Y := ⊤) le_top hCn hO2'
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨m, rfl⟩ := hRX hr
  have hmM : m ∈ M := hr
  have hdvd : orderOf (ρ m) ∣ orderOf m := orderOf_map_dvd ρ m
  have hoddr : Odd (orderOf (ρ m)) := Odd.of_dvd_nat (hodd m (hMC hmM)) hdvd
  obtain ⟨k, hk⟩ := hR2 ⟨ρ m, hr⟩
  have hk' : ρ m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd2 : orderOf (ρ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf (ρ m)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hoddr)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd2))

private theorem pCoreTwo_map_le_pCore {Hg : Type} [Group Hg] (Kg : Subgroup Hg) [Kg.Normal] :
    (CFSG.pCore 2 ↥Kg).map Kg.subtype ≤ CFSG.pCore 2 Hg := by
  refine le_sSup ⟨?_, (CFSG.pCore_isPGroup (p := 2) (G := ↥Kg)).map Kg.subtype⟩
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer (Kg : Set Hg) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    trivial
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Kg) (CFSG.pCore 2 ↥Kg) hg) n).mp hn

private theorem pCoreTwo_subgroupOf_le {Hg : Type} [Group Hg] (Kg : Subgroup Hg) :
    (CFSG.pCore 2 Hg).subgroupOf Kg ≤ CFSG.pCore 2 ↥Kg :=
  le_sSup ⟨(inferInstance : (CFSG.pCore 2 Hg).Normal).subgroupOf Kg,
    (CFSG.pCore_isPGroup (p := 2) (G := Hg)).comap_subtype⟩

private theorem pCoreTwo_quotient_pCore_eq_bot {Hg : Type} [Group Hg] :
    CFSG.pCore 2 (Hg ⧸ CFSG.pCore 2 Hg) = ⊥ := by
  set Q := CFSG.pCore 2 Hg with hQ
  set O := CFSG.pCore 2 (Hg ⧸ Q) with hO
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hK : IsPGroup 2 ↥(O.comap π) := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := Hg ⧸ Q)).comap_of_ker_isPGroup π ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := Hg)
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKQ : O.comap π ≤ Q := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ Q.map π := Subgroup.map_mono hKQ
    _ = ⊥ := QuotientGroup.map_mk'_self Q

private theorem pCoreTwo_pCoreOf_eq {G : Type*} [Group G] (X : Subgroup G) :
    pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := by
  unfold pCoreOf
  try with_reducible rfl

private theorem pCoreOf_le_pCoreTwo_of_perm {Hg : Type} [Group Hg] [Finite Hg] (K₁ : Subgroup Hg)
    (t : Hg) (hperm : ∀ x : Hg, x ∈ Subgroup.normalizer (K₁ : Set Hg) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set Hg)) :
    pCoreOf 2 K₁ ≤ CFSG.pCore 2 Hg := by
  set D : Subgroup Hg := Subgroup.normalizer (K₁ : Set Hg) with hD
  have hDt : ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
    intro d hd
    rcases hperm (t * d * t⁻¹) with h | h
    · exact h
    · have e : t⁻¹ * (t * d * t⁻¹) = d * t⁻¹ := by group
      rw [e] at h
      have hti : t⁻¹ ∈ D := by
        have := D.mul_mem (D.inv_mem hd) h
        simpa using this
      have ht : t ∈ D := by simpa using D.inv_mem hti
      exact D.mul_mem (D.mul_mem ht hd) (D.inv_mem ht)
  have hDn : D.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rcases hperm g with hg | hg
    · exact D.mul_mem (D.mul_mem hg hn) (D.inv_mem hg)
    · have e : g * n * g⁻¹ = t * ((t⁻¹ * g) * n * (t⁻¹ * g)⁻¹) * t⁻¹ := by group
      rw [e]
      exact hDt _ (D.mul_mem (D.mul_mem hg hn) (D.inv_mem hg))
  have h1 : pCoreOf 2 K₁ ≤ pCoreOf 2 D :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans Subgroup.le_normalizer)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have := hDn
  calc pCoreOf 2 K₁ ≤ pCoreOf 2 D := h1
    _ = (CFSG.pCore 2 ↥D).map D.subtype := pCoreTwo_pCoreOf_eq D
    _ ≤ CFSG.pCore 2 Hg := pCoreTwo_map_le_pCore D

theorem ar_facts_two_of_pCore_le {Hg : Type} [Group Hg] [Finite Hg] {V : Type} [CommGroup V]
    [Finite V]
    (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg)
    (hqK : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hKn : (K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom).Normal)
    (hcomm : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.pCore 2 Hg)
    (hQ : CFSG.pCore 2 Hg ≤ ρ.ker)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (hP : pCoreOf 2 K₁ ≤ CFSG.pCore 2 Hg)
    (hnt : ¬ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ≤ ρ.ker) :
    CFSG.IsQuasisimple ↥(K₁.map ρ) ∧
      CFSG.IsQuasisimple ↥((K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      (∀ a ∈ K₁.map ρ, ∀ b ∈ (K₁.map (MulAut.conj t).toMonoidHom).map ρ, a * b = b * a) ∧
      (K₁.map (MulAut.conj t).toMonoidHom).map ρ = (K₁.map ρ).map (MulAut.conj (ρ t)).toMonoidHom ∧
      (∀ x ∈ ρ.range, ∀ l ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ,
        x * l * x⁻¹ ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      (∀ x ∈ ρ.range, ∃ e : ℕ,
        x ^ 2 ^ e ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      pCoreOf 2 ρ.range = ⊥ := by
  set K₂ : Subgroup Hg := K₁.map (MulAut.conj t).toMonoidHom with hK₂
  set Q : Subgroup Hg := CFSG.pCore 2 Hg with hQdef
  have hP₁ : (CFSG.pCore 2 ↥K₁).map K₁.subtype ≤ Q := by
    rw [← pCoreTwo_pCoreOf_eq]
    exact hP
  set Z : Subgroup ↥K₁ := CFSG.pCore 2 ↥K₁ with hZdef
  set π : Hg →* Hg ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set ρ' : (Hg ⧸ Q) →* MulAut V := QuotientGroup.lift Q ρ hQ with hρ'
  set K₁' : Subgroup (Hg ⧸ Q) := K₁.map π with hK₁'
  set K₂' : Subgroup (Hg ⧸ Q) := K₂.map π with hK₂'
  have hZle : Z ≤ (π.comp K₁.subtype).ker := by
    intro z hz
    have h1 : (z : Hg) ∈ Q := hP₁ ⟨z, hz, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 h1
  set θ : (↥K₁ ⧸ Z) →* (Hg ⧸ Q) := QuotientGroup.lift Z (π.comp K₁.subtype) hZle with hθ
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro q hq1
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (k : Hg) ∈ Q := (QuotientGroup.eq_one_iff _).1 hq1
    exact (QuotientGroup.eq_one_iff _).2 (pCoreTwo_subgroupOf_le K₁ h1)
  have hθrange : θ.range = K₁' := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨QuotientGroup.mk ⟨k, hk⟩, rfl⟩
  have hKq₁ : CFSG.Open.IsQuasisimple ↥K₁' := by
    refine CFSG.ComponentClassification.Components.quasisimple_of_equiv ?_
      (B1Red.isQuasisimple_to_open hqK)
    exact ((MulEquiv.subgroupCongr hθrange.symm).trans (MonoidHom.ofInjective hθinj).symm)
  have hK₂'eq : K₂' = K₁'.map (MulAut.conj (π t)).toMonoidHom := by
    rw [hK₂', hK₂, hK₁', Subgroup.map_map, Subgroup.map_map]
    rfl
  have hKq₂ : CFSG.Open.IsQuasisimple ↥K₂' := by
    rw [hK₂'eq]
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (MulEquiv.subgroupMap (MulAut.conj (π t)) K₁').symm hKq₁
  have hc' : ∀ a ∈ K₁', ∀ b ∈ K₂', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ Q := hcomm (Subgroup.commutator_mem_commutator ha hb)
    have h3 : ⁅π a, π b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hsup : K₁' ⊔ K₂' = (K₁ ⊔ K₂).map π := (Subgroup.map_sup K₁ K₂ π).symm
  have hN' : (K₁' ⊔ K₂').Normal := by
    rw [hsup]
    exact Subgroup.Normal.map hKn π hπs
  have hO2 : CFSG.pCore 2 (Hg ⧸ Q) = ⊥ := pCoreTwo_quotient_pCore_eq_bot
  have h2' : ∀ y : Hg ⧸ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁' ⊔ K₂' := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, he⟩ := h2 y
    refine ⟨e, ?_⟩
    rw [hsup, ← QuotientGroup.mk_pow]
    exact Subgroup.mem_map_of_mem π he
  have hnt₁ : ¬ K₁ ≤ ρ.ker := by
    intro h
    refine hnt (sup_le h ?_)
    rintro _ ⟨k, hk, rfl⟩
    rw [MonoidHom.mem_ker]
    have hk1 : ρ k = 1 := h hk
    simp [MulAut.conj_apply, hk1]
  have hnt₂ : ¬ K₂ ≤ ρ.ker := by
    intro h
    refine hnt (sup_le ?_ h)
    intro k hk
    have h1 : ρ (t * k * t⁻¹) = 1 := h ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rw [MonoidHom.mem_ker]
    have h3 : ρ t * ρ k * (ρ t)⁻¹ = 1 := by simpa using h1
    simpa using h3
  have hnt₁' : ¬ K₁' ≤ ρ'.ker := by
    intro h
    apply hnt₁
    intro k hk
    exact h (Subgroup.mem_map_of_mem π hk)
  have hnt₂' : ¬ K₂' ≤ ρ'.ker := by
    intro h
    apply hnt₂
    intro k hk
    exact h (Subgroup.mem_map_of_mem π hk)
  obtain ⟨hL₁, hL₂, hO2'⟩ := ar_coreTwo ρ' K₁' K₂' hKq₁ hKq₂ hc' hN' hO2 h2' hnt₁' hnt₂'
  have hmap₁ : K₁'.map ρ' = K₁.map ρ := by
    rw [hK₁', Subgroup.map_map]
    rfl
  have hmap₂ : K₂'.map ρ' = K₂.map ρ := by
    rw [hK₂', Subgroup.map_map]
    rfl
  have hrange : ρ'.range = ρ.range := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨π h, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmap₁]
    exact B1Red.isQuasisimple_of_open hL₁
  · rw [← hmap₂]
    exact B1Red.isQuasisimple_of_open hL₂
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ ρ.ker := hQ (hcomm (Subgroup.commutator_mem_commutator ha hb))
    have h3 : ⁅ρ a, ρ b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  · rw [hK₂, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  · intro x hx l hl
    rw [← Subgroup.map_sup] at hl ⊢
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨n, hn, rfl⟩ := hl
    exact ⟨h * n * h⁻¹, hKn.conj_mem n hn h, by simp⟩
  · rintro _ ⟨h, rfl⟩
    obtain ⟨e, he⟩ := h2 h
    refine ⟨e, ?_⟩
    rw [← Subgroup.map_sup, ← map_pow]
    exact Subgroup.mem_map_of_mem _ he
  · rw [← hrange]
    exact hO2'

theorem ar_facts_two {Hg : Type} [Group Hg] [Finite Hg] {V : Type} [CommGroup V] [Finite V]
    (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg)
    (hqK : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hKn : (K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom).Normal)
    (hcomm : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.pCore 2 Hg)
    (hQ : CFSG.pCore 2 Hg ≤ ρ.ker)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (hperm : ∀ x : Hg, x ∈ Subgroup.normalizer (K₁ : Set Hg) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set Hg))
    (hnt : ¬ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ≤ ρ.ker) :
    CFSG.IsQuasisimple ↥(K₁.map ρ) ∧
      CFSG.IsQuasisimple ↥((K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      (∀ a ∈ K₁.map ρ, ∀ b ∈ (K₁.map (MulAut.conj t).toMonoidHom).map ρ, a * b = b * a) ∧
      (K₁.map (MulAut.conj t).toMonoidHom).map ρ = (K₁.map ρ).map (MulAut.conj (ρ t)).toMonoidHom ∧
      (∀ x ∈ ρ.range, ∀ l ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ,
        x * l * x⁻¹ ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      (∀ x ∈ ρ.range, ∃ e : ℕ,
        x ^ 2 ^ e ∈ K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      pCoreOf 2 ρ.range = ⊥ :=
  ar_facts_two_of_pCore_le ρ K₁ t hqK hKn hcomm hQ h2 (pCoreOf_le_pCoreTwo_of_perm K₁ t hperm) hnt

end S153M

end CFSG.Quasithin
