module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfE

public section

namespace CFSG.Quasithin.H13.L34Br

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {Y : Type} [Group Y]

theorem mult_zmod_two_cases (m : Multiplicative (ZMod 2)) :
    m = 1 ∨ m = Multiplicative.ofAdd 1 := by
  revert m
  decide

theorem psi_conj (ψ : Y →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (g x : Y) :
    ψ (g * x * g⁻¹) = ψ x := by
  rw [map_mul, map_mul, mul_comm (ψ g) (ψ x), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    mul_one]

theorem mem_pCoreOf_centralizer [Finite Y] {b : Y} (hbb : b * b = 1) :
    b ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.zpowers b ≤ Subgroup.centralizer ({b} : Set Y) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hN : Subgroup.centralizer ({b} : Set Y) ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup Y) : Set Y) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    have hcb := Subgroup.mem_centralizer_singleton_iff.1 hc
    have key : ∀ n : ℤ, c * b ^ n * c⁻¹ = b ^ n := fun n => by
      have : Commute c b := hcb
      rw [(this.zpow_right n).eq, mul_inv_cancel_right]
    intro h
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (key n).symm⟩
    · rintro ⟨n, hn⟩
      have hn' : b ^ n = c * h * c⁻¹ := hn
      have h2 : c * h * c⁻¹ = c * b ^ n * c⁻¹ := hn'.symm.trans (key n).symm
      have h3 : h = b ^ n := by simpa using h2
      exact ⟨n, h3.symm⟩
  have hp : IsPGroup 2 (Subgroup.zpowers b) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hbb, one_zpow]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hN hp (Subgroup.mem_zpowers b)

variable [Finite Y]

omit [Finite Y] in
theorem psi_eq_graph {S E : Subgroup Y}
    {ψ : Y →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)}
    (hψinn : ∀ x : Y, x * x = 1 → ψ x = 1 → x ∈ oTwoUpper (⊤ : Subgroup Y))
    (hψfield : ∀ x ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y),
      (ψ x).1 = Multiplicative.ofAdd 1 → ∃ d ∈ oTwoUpper (⊤ : Subgroup Y),
        d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) ∧
          x * d * x⁻¹ * d⁻¹ ∉ S)
    (hES : E ≤ S) (hEe : IsElemAbelian 2 E)
    (hB : ∀ x ∈ E, ∀ d ∈ oTwoUpper (⊤ : Subgroup Y),
      d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) →
        x * d * x⁻¹ * d⁻¹ ∈ S)
    {x : Y} (hxE : x ∈ E) (hxK : x ∉ oTwoUpper (⊤ : Subgroup Y)) :
    ψ x = (1, Multiplicative.ofAdd 1) := by
  have : (oTwoUpper (⊤ : Subgroup Y)).Normal := oTwoUpper_top_normal'
  have hxx : x * x = 1 := by rw [← sq]; exact hEe.2 x hxE
  have h1 : (ψ x).1 = 1 := by
    rcases mult_zmod_two_cases (ψ x).1 with h | h
    · exact h
    · exfalso
      obtain ⟨d, hdK, hdN, hdS⟩ := hψfield x (le_normalizer_inf_normal (hES hxE)) h
      exact hdS (hB x hxE d hdK hdN)
  rcases mult_zmod_two_cases (ψ x).2 with h2 | h2
  · exact absurd (hψinn x hxx (Prod.ext h1 h2)) hxK
  · exact Prod.ext h1 h2

theorem graph_centralizer
    {ψ : Y →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)}
    (hψP : ∀ b : Y, b * b = 1 → ψ b = (1, Multiplicative.ofAdd 1) →
      IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)))
    {b : Y} (hbb : b * b = 1) (hψb : ψ b = (1, Multiplicative.ofAdd 1)) :
    IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥(Subgroup.centralizer ({b} : Set Y)) ⧸
        CFSG.pCore 2 ↥(Subgroup.centralizer ({b} : Set Y))))) ∧
      oTwoUpper (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y) ⊓
        pCoreOf 2 (Subgroup.centralizer ({b} : Set Y)) ≤ ⊥ :=
  isPSL_oTwoUpper_quot_of_bot inf_le_right (fun w hw => by
    obtain ⟨n, hn⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup Y) (Subgroup.mem_top w)
    exact ⟨n, Subgroup.mem_inf.2 ⟨hn, Subgroup.pow_mem _ hw _⟩⟩) (hψP b hbb hψb)

theorem exists_goodPair_of_not_le {S E : Subgroup Y} (hS : IsSylowIn 2 S ⊤) (hout : OutY S)
    (hES : E ≤ S) (hEe : IsElemAbelian 2 E) (hEK : ¬ E ≤ oTwoUpper ⊤)
    (hB : ∀ x ∈ E, ∀ d ∈ oTwoUpper (⊤ : Subgroup Y),
      d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) →
        x * d * x⁻¹ * d⁻¹ ∈ S) :
    ∃ y : Y, ∃ Y₁ : Subgroup Y, GoodPair S (E.map (MulAut.conj y).toMonoidHom) Y₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper (⊤ : Subgroup Y) with hK
  have hKn : K.Normal := oTwoUpper_top_normal'
  obtain ⟨ψ, hψK, hψinn, hψP, hψfield⟩ := hout
  have hgraph : ∀ x ∈ E, x ∉ K → ψ x = (1, Multiplicative.ofAdd 1) := fun x hx hxK =>
    psi_eq_graph hψinn hψfield hES hEe hB hx hxK
  have hgg : (1, Multiplicative.ofAdd (1 : ZMod 2)) * (1, Multiplicative.ofAdd 1) =
      (1 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
    refine Prod.ext ?_ ?_
    · show (1 : Multiplicative (ZMod 2)) * 1 = 1
      exact mul_one 1
    · show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
      rw [← ofAdd_add, show (1 + 1 : ZMod 2) = 0 from rfl, ofAdd_zero]
  obtain ⟨a, haE, haK⟩ := Set.not_subset.1 hEK
  have hEC : E ≤ Subgroup.centralizer ({a} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hEe.1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥E) ⟨a, haE⟩))
  have hE2 : IsPGroup 2 E := isPGroup_of_isElemAbelian hEe
  obtain ⟨S₁, hS₁, hES₁⟩ := exists_isSylowIn_ge 2 hEC hE2
  obtain ⟨y₁, -, hy₁⟩ := exists_conj_le_of_isSylowIn hS le_top hS₁.2.1
  set a₁ := y₁ * a * y₁⁻¹ with ha₁
  set E₁ := E.map (MulAut.conj y₁).toMonoidHom with hE₁
  have hCa₁ := centralizer_conj_singleton y₁ a
  rw [← ha₁] at hCa₁
  have hS₁' : IsSylowIn 2 (S₁.map (MulAut.conj y₁).toMonoidHom)
      (Subgroup.centralizer ({a₁} : Set Y)) := hCa₁ ▸ isSylowIn_map_conj hS₁ y₁
  have hT₁ : IsSylowIn 2 (S ⊓ Subgroup.centralizer ({a₁} : Set Y))
      (Subgroup.centralizer ({a₁} : Set Y)) :=
    isSylowIn_of_le hS₁' (le_inf hy₁ hS₁'.1) inf_le_right (hS.2.1.to_le inf_le_left)
  have hE₁S : E₁ ≤ S := (Subgroup.map_mono hES₁).trans hy₁
  have ha₁E₁ : a₁ ∈ E₁ := ⟨a, haE, rfl⟩
  have haa : a * a = 1 := by rw [← sq]; exact hEe.2 a haE
  have ha₁a₁ : a₁ * a₁ = 1 := by
    rw [ha₁]
    calc y₁ * a * y₁⁻¹ * (y₁ * a * y₁⁻¹) = y₁ * (a * a) * y₁⁻¹ := by group
      _ = 1 := by rw [haa]; group
  have hψa₁ : ψ a₁ = (1, Multiplicative.ofAdd 1) := (psi_conj ψ y₁ a).trans (hgraph a haE haK)
  have hE₁e : IsElemAbelian 2 E₁ := isElemAbelian_map _ hEe
  have hE₁C : E₁ ≤ Subgroup.centralizer ({a₁} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hE₁e.1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥E₁) ⟨a₁, ha₁E₁⟩))
  have hsingle : ∀ {F : Subgroup Y} {f : Y}, f ∈ F →
      Subgroup.centralizer (F : Set Y) ≤ Subgroup.centralizer ({f} : Set Y) := fun hf =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hf)
  by_cases hE₁K : E₁ ⊓ K = ⊥
  swap
  ·
    obtain ⟨hPSL, hO⟩ := graph_centralizer hψP ha₁a₁ hψa₁
    refine ⟨y₁, Subgroup.centralizer ({a₁} : Set Y), hE₁S, hE₁C,
      fun x hx => hsingle ha₁E₁ (Subgroup.mem_inf.1 hx).2, hT₁, hPSL, fun h => hE₁K ?_⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE₁, hxK⟩ := Subgroup.mem_inf.1 hx
    exact hO (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxK, hE₁C hxE₁⟩, h hxE₁⟩)
  have hE₁a : ∀ x ∈ E₁, x = 1 ∨ x = a₁ := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    have hxK : x ∉ K := fun h => hx1 (by
      have : x ∈ E₁ ⊓ K := Subgroup.mem_inf.2 ⟨hx, h⟩
      rwa [hE₁K, Subgroup.mem_bot] at this)
    obtain ⟨x', hx', rfl⟩ := hx
    have hx'K : x' ∉ K := fun h => hxK (hKn.conj_mem x' h y₁)
    have hψx : ψ (y₁ * x' * y₁⁻¹) = (1, Multiplicative.ofAdd 1) :=
      (psi_conj ψ y₁ x').trans (hgraph x' hx' hx'K)
    have hmem : y₁ * x' * y₁⁻¹ * a₁ ∈ E₁ := E₁.mul_mem ⟨x', hx', rfl⟩ ha₁E₁
    have hprod : y₁ * x' * y₁⁻¹ * a₁ ∈ E₁ ⊓ K := by
      refine Subgroup.mem_inf.2 ⟨hmem, hψinn _ ?_ ?_⟩
      · rw [← sq]
        exact hE₁e.2 _ hmem
      · rw [map_mul, hψx, hψa₁, hgg]
    rw [hE₁K, Subgroup.mem_bot] at hprod
    exact (mul_eq_one_iff_eq_inv.1 hprod).trans (inv_eq_of_mul_eq_one_right ha₁a₁)
  set T₁ := S ⊓ Subgroup.centralizer ({a₁} : Set Y) with hT₁def
  have hT₁2 : IsPGroup 2 T₁ := hT₁.2.1
  have hP₁ := hψP a₁ ha₁a₁ hψa₁
  have h60 := card_of_isPSL_two hP₁
  have hCN : Subgroup.centralizer ({a₁} : Set Y) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({a₁} : Set Y) : Subgroup Y) : Set Y) :=
    le_normalizer_inf' (by rw [Subgroup.normalizer_eq_top]; exact le_top) Subgroup.le_normalizer
  have hTP : IsSylowIn 2 (T₁ ⊓ (K ⊓ Subgroup.centralizer ({a₁} : Set Y)))
      (K ⊓ Subgroup.centralizer ({a₁} : Set Y)) :=
    B6.isSylowTwoOf_inf_normal hT₁ inf_le_right hCN
  have hTK : T₁ ⊓ K ≠ ⊥ := by
    intro h
    have h' : T₁ ⊓ (K ⊓ Subgroup.centralizer ({a₁} : Set Y)) = ⊥ := by
      rw [eq_bot_iff, ← h]
      exact le_inf inf_le_left (inf_le_right.trans inf_le_left)
    have hi := hTP.2.2
    rw [h', Subgroup.relIndex_bot_left, h60] at hi
    exact hi (by norm_num)
  have hnil : Group.IsNilpotent ↥T₁ := hT₁2.isNilpotent
  set N₀ := (T₁ ⊓ K).subgroupOf T₁ with hN₀
  have hN₀n : N₀.Normal := ⟨fun n hn g => by
    rw [hN₀, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnT, hnK⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, hKn.conj_mem _ hnK g⟩
    simpa using T₁.mul_mem (T₁.mul_mem g.2 hnT) (T₁.inv_mem g.2)⟩
  have hN₀1 : N₀ ≠ ⊥ := by
    intro h
    apply hTK
    rw [eq_bot_iff]
    intro x hx
    have hxT : x ∈ T₁ := (Subgroup.mem_inf.1 hx).1
    have : (⟨x, hxT⟩ : ↥T₁) ∈ N₀ := by
      rw [hN₀, Subgroup.mem_subgroupOf]
      exact hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN₀1
  have hZ2 : IsPGroup 2 ↥(N₀ ⊓ Subgroup.center ↥T₁) :=
    hT₁2.to_subgroup _
  have hntZ : Nontrivial ↥(N₀ ⊓ Subgroup.center ↥T₁) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hZ2
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := ↥(N₀ ⊓ Subgroup.center ↥T₁))
    rw [hm, pow_zero] at this
    exact lt_irrefl _ this
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2
    (show 2 ∣ Nat.card ↥(N₀ ⊓ Subgroup.center ↥T₁) by
      rw [hm]
      exact dvd_pow_self 2 hm0)
  set z : Y := (((z₀ : ↥T₁)) : Y) with hz
  have hzT : z ∈ T₁ := (z₀ : ↥T₁).2
  have hz₀N : (z₀ : ↥T₁) ∈ N₀ := (Subgroup.mem_inf.1 z₀.2).1
  have hz₀Z : (z₀ : ↥T₁) ∈ Subgroup.center ↥T₁ := (Subgroup.mem_inf.1 z₀.2).2
  have hzK : z ∈ K := by
    have : z ∈ T₁ ⊓ K := hz₀N
    exact (Subgroup.mem_inf.1 this).2
  have hzc : ∀ t ∈ T₁, t * z = z * t := by
    intro t ht
    have hc := Subgroup.mem_center_iff.1 hz₀Z ⟨t, ht⟩
    exact congrArg Subtype.val hc
  have hzo : orderOf z = 2 := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz₀
  have hzz : z * z = 1 := by rw [← sq, ← hzo]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at hzo
    norm_num at hzo
  have ha₁T : a₁ ∈ T₁ := Subgroup.mem_inf.2 ⟨hE₁S ha₁E₁,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hza₁ : a₁ * z = z * a₁ := hzc a₁ ha₁T
  obtain ⟨b, hb⟩ : ∃ b : Y, b = a₁ * z := ⟨_, rfl⟩
  have hbb : b * b = 1 := by
    rw [hb]
    calc a₁ * z * (a₁ * z) = a₁ * (z * a₁) * z := by group
      _ = a₁ * (a₁ * z) * z := by rw [hza₁]
      _ = (a₁ * a₁) * (z * z) := by group
      _ = 1 := by rw [ha₁a₁, hzz, one_mul]
  have hψb : ψ b = (1, Multiplicative.ofAdd 1) := by
    rw [hb, map_mul, hψa₁, hψK z hzK, mul_one]
  have hTb : T₁ ≤ Subgroup.centralizer ({b} : Set Y) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hta : t * a₁ = a₁ * t :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2
    rw [hb]
    calc t * (a₁ * z) = a₁ * (t * z) := by rw [← mul_assoc, hta, mul_assoc]
      _ = a₁ * (z * t) := by rw [hzc t ht]
      _ = a₁ * z * t := by group
  obtain ⟨S₂, hS₂, hTS₂⟩ := exists_isSylowIn_ge 2 hTb hT₁2
  obtain ⟨y₂, -, hy₂⟩ := exists_conj_le_of_isSylowIn hS le_top hS₂.2.1
  set b₂ := y₂ * b * y₂⁻¹ with hb₂
  set a₂ := y₂ * a₁ * y₂⁻¹ with ha₂
  set E₂ := E₁.map (MulAut.conj y₂).toMonoidHom with hE₂
  have hCb₂ := centralizer_conj_singleton y₂ b
  rw [← hb₂] at hCb₂
  have hCa₂ := centralizer_conj_singleton y₂ a₁
  rw [← ha₂] at hCa₂
  have hS₂' : IsSylowIn 2 (S₂.map (MulAut.conj y₂).toMonoidHom)
      (Subgroup.centralizer ({b₂} : Set Y)) := hCb₂ ▸ isSylowIn_map_conj hS₂ y₂
  have hE₁T : E₁ ≤ T₁ := le_inf hE₁S hE₁C
  have ha₂E₂ : a₂ ∈ E₂ := ⟨a₁, ha₁E₁, rfl⟩
  have hE₂a : ∀ x ∈ E₂, x = 1 ∨ x = a₂ := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hE₁a x hx with rfl | rfl
    · left
      simp
    · right
      rfl
  have hE₂C : E₂ ≤ Subgroup.centralizer ({b₂} : Set Y) := by
    rw [hCb₂, hE₂]
    exact Subgroup.map_mono (hE₁T.trans hTb)
  have hQ' : T₁.map (MulAut.conj y₂).toMonoidHom ≤ S ⊓ Subgroup.centralizer ({a₂} : Set Y) := by
    refine le_inf ((Subgroup.map_mono hTS₂).trans hy₂) ?_
    rw [hCa₂]
    exact Subgroup.map_mono inf_le_right
  have hT₁' : IsSylowIn 2 (T₁.map (MulAut.conj y₂).toMonoidHom)
      (Subgroup.centralizer ({a₂} : Set Y)) := hCa₂ ▸ isSylowIn_map_conj hT₁ y₂
  have hQeq : T₁.map (MulAut.conj y₂).toMonoidHom = S ⊓ Subgroup.centralizer ({a₂} : Set Y) :=
    Subgroup.eq_of_le_of_card_ge hQ' (card_le_of_isSylowIn hT₁' inf_le_right
      (hS.2.1.to_le inf_le_left))
  have hCE₂ : S ⊓ Subgroup.centralizer (E₂ : Set Y) ≤ Subgroup.centralizer ({b₂} : Set Y) := by
    intro x hx
    obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxa : x ∈ S ⊓ Subgroup.centralizer ({a₂} : Set Y) :=
      Subgroup.mem_inf.2 ⟨hxS, hsingle ha₂E₂ hxC⟩
    rw [← hQeq] at hxa
    rw [hCb₂]
    exact Subgroup.map_mono hTb hxa
  obtain ⟨hPSL, hO⟩ := graph_centralizer hψP (b := b₂)
    (by
      rw [hb₂]
      calc y₂ * b * y₂⁻¹ * (y₂ * b * y₂⁻¹) = y₂ * (b * b) * y₂⁻¹ := by group
        _ = 1 := by rw [hbb]; group)
    ((psi_conj ψ y₂ b).trans hψb)
  refine ⟨y₂ * y₁, Subgroup.centralizer ({b₂} : Set Y), ?_⟩
  rw [← map_conj_map_conj', ← hE₁, ← hE₂]
  refine ⟨(Subgroup.map_mono (hE₁T.trans hTS₂)).trans hy₂, hE₂C, hCE₂,
    isSylowIn_of_le hS₂' (le_inf hy₂ hS₂'.1) inf_le_right (hS.2.1.to_le inf_le_left), hPSL,
    fun h => hz1 ?_⟩
  have hb₂O := mem_pCoreOf_centralizer (b := b₂) (by
    rw [hb₂]
    calc y₂ * b * y₂⁻¹ * (y₂ * b * y₂⁻¹) = y₂ * (b * b) * y₂⁻¹ := by group
      _ = 1 := by rw [hbb]; group)
  have hab : a₂ * b₂ = y₂ * z * y₂⁻¹ := by
    rw [ha₂, hb₂, hb]
    calc y₂ * a₁ * y₂⁻¹ * (y₂ * (a₁ * z) * y₂⁻¹) = y₂ * ((a₁ * a₁) * z) * y₂⁻¹ := by group
      _ = y₂ * z * y₂⁻¹ := by rw [ha₁a₁, one_mul]
  have hmem : a₂ * b₂ ∈ oTwoUpper (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ({b₂} : Set Y) ⊓
      pCoreOf 2 (Subgroup.centralizer ({b₂} : Set Y)) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mul_mem _ (h ha₂E₂) hb₂O⟩
    · rw [hab]
      exact hKn.conj_mem z hzK y₂
    · exact Subgroup.mul_mem _ (hE₂C ha₂E₂) (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have h1 := Subgroup.mem_bot.1 (hO hmem)
  rw [hab] at h1
  calc z = y₂⁻¹ * (y₂ * z * y₂⁻¹) * y₂ := by group
    _ = 1 := by rw [h1]; group

theorem exists_goodPair {S E : Subgroup Y} (hS : IsSylowIn 2 S ⊤) (hpar : ParY S)
    (hout : OutY S) (hES : E ≤ S) (hEe : IsElemAbelian 2 E) (hE1 : E ≠ ⊥)
    (hB : ∀ x ∈ E, ∀ d ∈ oTwoUpper (⊤ : Subgroup Y),
      d ∈ Subgroup.normalizer ((S ⊓ oTwoUpper ⊤ : Subgroup Y) : Set Y) →
        x * d * x⁻¹ * d⁻¹ ∈ S) :
    ∃ y : Y, ∃ Y₁ : Subgroup Y, GoodPair S (E.map (MulAut.conj y).toMonoidHom) Y₁ := by
  by_cases hEK : E ≤ oTwoUpper ⊤
  · exact exists_goodPair_of_le hS hpar (le_inf hES hEK) hEe hE1
  · exact exists_goodPair_of_not_le hS hout hES hEe hEK hB

end CFSG.Quasithin.H13.L34Br
