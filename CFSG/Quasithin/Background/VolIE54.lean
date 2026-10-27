module

public import CFSG.Quasithin.Background.E5Two
public import CFSG.Quasithin.Background.F918C3
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.VolI

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

namespace E54

section Thompson

variable {G : Type} [Group G]

theorem omegaOneCenterOf_bot_eq : omegaOneCenterOf (⊥ : Subgroup G) = ⊥ :=
  le_bot_iff.mp (omegaOneCenterOf_le ⊥)

variable [Finite G]

theorem card_le_two_pow_pRank_of_le {E H : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ CFSG.Open.pRank 2 H := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian H
  have h := (isMaxElemAbelian_iff_corank_zero.mp hA₀).2.2
  rw [pow_zero, mul_one] at h
  exact h ▸ hA₀.2.2 E hEH hE

theorem thompsonJi_eq_bot_of_le {P : Subgroup G} {j : ℕ} (hj : CFSG.Open.pRank 2 P ≤ j) :
    thompsonJi P j = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun A hA => ?_)
  have h1 : Nat.card A * 2 ^ j ≤ 1 * 2 ^ j := by
    rw [hA.2.2, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) hj
  have h2 : Nat.card A ≤ 1 := Nat.le_of_mul_le_mul_right h1 (by positivity)
  exact (Subgroup.card_eq_one.mp (le_antisymm h2 Nat.card_pos)).le

theorem thompsonJi_eq_thompsonJk {P : Subgroup G} {j : ℕ} (hj : j < CFSG.Open.pRank 2 P) :
    thompsonJi P j = H13.thompsonJk j P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine iSup₂_le fun A hA => E5.le_thompsonJk hA.1 hA.2.1 fun B hBP hB => ?_
    calc Nat.card B ≤ 2 ^ CFSG.Open.pRank 2 P := card_le_two_pow_pRank_of_le hBP hB
      _ = 2 ^ j * Nat.card A := by rw [← hA.2.2, mul_comm]
  · refine iSup₂_le fun A hA => ?_
    intro a ha
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
    have hA₀c := (isMaxElemAbelian_iff_corank_zero.mp hA₀).2.2
    rw [pow_zero, mul_one] at hA₀c
    have hAc : 2 ^ CFSG.Open.pRank 2 P ≤ 2 ^ j * Nat.card A := hA₀c ▸ hA.2.2 A₀ hA₀.1 hA₀.2.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (B2F.isPGroup_of_isElemAbelian hA.2.1)
    have hkm : CFSG.Open.pRank 2 P - j ≤ k := by
      rw [hk, ← pow_add] at hAc
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hAc
      omega
    have hdvd : 2 ^ (CFSG.Open.pRank 2 P - j) ∣ Nat.card A := by
      rw [hk]
      exact pow_dvd_pow 2 hkm
    have hza : Nat.card (Subgroup.zpowers a) ∣ 2 ^ (CFSG.Open.pRank 2 P - j) := by
      rw [Nat.card_zpowers]
      have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hA.2.1.2 a ha)
      exact h2.trans (dvd_pow_self 2 (by omega))
    obtain ⟨K, hKc, haK, hKA⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hza hdvd
        (Subgroup.zpowers_le.mpr ha)
    have hK : IsElemAbelianCorank P j K :=
      ⟨hKA.trans hA.1, B2F.isElemAbelian_mono hKA hA.2.1, by
        rw [hKc, ← pow_add, Nat.sub_add_cancel hj.le]⟩
    exact le_iSup₂_of_le (f := fun A (_ : IsElemAbelianCorank P j A) => A) K hK le_rfl
      (haK (Subgroup.mem_zpowers a))

end Thompson

theorem pCore_two_quotient_eq_bot {H : Type*} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set Q := CFSG.pCore 2 H with hQ
  set O := CFSG.pCore 2 (H ⧸ Q) with hO
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hK : IsPGroup 2 ↥(O.comap π) := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := H ⧸ Q)).comap_of_ker_isPGroup π ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := H)
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKQ : O.comap π ≤ Q := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ Q.map π := Subgroup.map_mono hKQ
    _ = ⊥ := QuotientGroup.map_mk'_self Q

theorem mk_pCore_eq_one_iff {Γ : Type*} [Group Γ] (X : Subgroup Γ) (y : ↥X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥X) y = 1 ↔ (y : Γ) ∈ pCoreOf 2 X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← Subtype.ext hzy]

theorem exists_section_of_odd {Γ : Type} [Group Γ] [Finite Γ] {X Q E : Subgroup Γ}
    (hQ : IsPGroup 2 Q) (hEQ : E ≤ Q) (hQX : Q ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set Γ))
    (hXE : X ≤ Subgroup.normalizer (E : Set Γ)) {x : Γ} (hxX : x ∈ X) (hodd : Odd (orderOf x))
    (hxE : x ∉ Subgroup.centralizer (E : Set Γ)) :
    ∃ E' : Subgroup Γ, E' ≤ E ∧ X ≤ Subgroup.normalizer (E' : Set Γ) ∧
      X ≤ Subgroup.normalizer ((⁅E', Q⁆ : Subgroup Γ) : Set Γ) ∧
        ∃ e ∈ E', x * e * x⁻¹ * e⁻¹ ∉ ⁅E', Q⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Subgroup Γ → Subgroup Γ := fun H => ⁅H, Q⁆
  let ser : ℕ → Subgroup Γ := fun n => f^[n] E
  have hserS : ∀ n, ser (n + 1) = ⁅ser n, Q⁆ := fun n => Function.iterate_succ_apply' f n E
  have hN : ∀ n, X ≤ Subgroup.normalizer (ser n : Set Γ) := by
    intro n
    induction n with
    | zero => exact hXE
    | succ n ih =>
      rw [hserS]
      exact F9.le_normalizer_commutator_of_le ih hXQ
  have hle : ∀ n, ser (n + 1) ≤ ser n := fun n => by
    rw [hserS, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hQX.trans (hN n))
  have hleE : ∀ n, ser n ≤ E := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (hle n).trans ih
  have hlcs : ∀ n, ser n ≤ Q.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact hEQ
    | succ n ih =>
      rw [hserS, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mono ih le_rfl
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  obtain ⟨N, hNbot⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Q).mp hnil
  have hserN : ser N = ⊥ := by
    have h := hlcs N
    rw [hNbot] at h
    exact le_bot_iff.mp h
  have hex : ∃ n, x ∈ Subgroup.centralizer (ser n : Set Γ) := ⟨N, by
    rw [hserN, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]⟩
  have hn₀ : Nat.find hex ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex
    rw [h0] at h
    exact hxE h
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hn₀
  have hxn1 : x ∈ Subgroup.centralizer (ser (n + 1) : Set Γ) := by
    rw [← hn]
    exact Nat.find_spec hex
  have hxn : x ∉ Subgroup.centralizer (ser n : Set Γ) := Nat.find_min hex (by omega)
  refine ⟨ser n, hleE n, hN n, ?_, ?_⟩
  · rw [← hserS]
    exact hN (n + 1)
  · by_contra hall
    push Not at hall
    apply hxn
    refine E5.mem_centralizer_of_odd (hle n) (hQ.to_le ((hleE n).trans hEQ)) hxn1
      (E5.mem_quotStab_iff.mpr ⟨hN (n + 1) hxX, fun q hq => ?_⟩) hodd
    rw [hserS, commutatorElement_def]
    exact hall q hq

theorem commutator_mem_and_sq_mem {Γ : Type} [Group Γ] [Finite Γ] {X C : Subgroup Γ}
    (hqs : CFSG.IsQuasisimple ↥(CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X))))
    (h2 : ∀ q : O2Q X, ∃ e : ℕ, q ^ 2 ^ e ∈ CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X)))
    (hQC : pCoreOf 2 X ≤ C) (hCX : C ≤ X) (hXC : X ≤ Subgroup.normalizer (C : Set Γ))
    {x : Γ} (hxX : x ∈ X) (hodd : Odd (orderOf x)) (hxC : x ∉ C) :
    (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ pCoreOf 2 X) ∧
      ∀ a ∈ C, a ^ 2 = 1 → a ∈ pCoreOf 2 X := by
  classical
  set Q := pCoreOf 2 X with hQdef
  set Ks := CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X)) with hKsdef
  set π : ↥X →* O2Q X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : ↥X, π y = 1 ↔ (y : Γ) ∈ Q := mk_pCore_eq_one_iff X
  set Cs : Subgroup (O2Q X) := (C.subgroupOf X).map π with hCsdef
  have hCn : (C.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXC
  have hCsn : Cs.Normal := hCn.map π hπs
  have hKsn : Ks.Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (le_normalizer_quasithinGenFitting (⊤ : Subgroup (O2Q X))))
  set xb : O2Q X := π ⟨x, hxX⟩ with hxbdef
  have hxbK : xb ∈ Ks := by
    obtain ⟨e, he⟩ := h2 xb
    have hdvd : orderOf xb ∣ orderOf x := by
      have h := orderOf_map_dvd π (⟨x, hxX⟩ : ↥X)
      rwa [Subgroup.orderOf_mk] at h
    have hcop : Nat.Coprime (2 ^ e) (orderOf xb) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr (Odd.of_dvd_nat hodd hdvd))
    exact (Subgroup.zpowers_le.mpr he) (A4.mem_zpowers_pow_of_coprime hcop)
  have hxbC : xb ∉ Cs := by
    rintro ⟨c, hc, hcx⟩
    apply hxC
    have h1 : π (c⁻¹ * ⟨x, hxX⟩) = 1 := by
      rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have h3 : ((c⁻¹ * ⟨x, hxX⟩ : ↥X) : Γ) ∈ C := hQC ((hker _).mp h1)
    have h4 : x = (c : Γ) * ((c⁻¹ * ⟨x, hxX⟩ : ↥X) : Γ) := by simp
    rw [h4]
    exact C.mul_mem hc h3
  have hcent : Cs.subgroupOf Ks ≤ Subgroup.center ↥Ks := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (hCsn.subgroupOf Ks) with h | h
    · exfalso
      apply hxbC
      have hmem : (⟨xb, hxbK⟩ : ↥Ks) ∈ Cs.subgroupOf Ks := by
        rw [h]
        exact Subgroup.mem_top _
      exact hmem
    · exact h
  have hcomm : ⁅Ks, Cs⁆ ≤ Subgroup.centralizer (Ks : Set (O2Q X)) := by
    intro z hz
    have hz' : z ∈ Ks ⊓ Cs := Subgroup.commutator_le_inf Ks Cs hz
    have hzc := hcent (show (⟨z, hz'.1⟩ : ↥Ks) ∈ Cs.subgroupOf Ks from hz'.2)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨k, hk⟩)
  have hKC : ⁅Ks, Cs⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hqs.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm)
  have hCsC : Cs ≤ Subgroup.centralizer (Ks : Set (O2Q X)) := by
    rw [Subgroup.commutator_comm] at hKC
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKC
  have hCsK : Cs ≤ Ks := fun c hc =>
    centralizer_quasithinGenFitting_le (⊤ : Subgroup (O2Q X)) ⟨Subgroup.mem_top c, hCsC hc⟩
  have hab : ∀ a ∈ Cs, ∀ b ∈ Cs, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hCsC ha) b (hCsK hb)).symm
  let Ω : Subgroup (O2Q X) :=
    { carrier := {y | y ∈ Cs ∧ y ^ 2 = 1}
      one_mem' := ⟨Cs.one_mem, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨Cs.mul_mem ha hb, ?_⟩
        rw [Commute.mul_pow (hab a ha b hb) 2, ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨Cs.inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ }
  have hΩn : Ω.Normal := ⟨fun y hy g => ⟨hCsn.conj_mem y hy.1 g, by
    rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩⟩
  have hΩ2 : IsPGroup 2 Ω := fun y => ⟨1, Subtype.ext (by simpa using y.2.2)⟩
  have hO : CFSG.pCore 2 (O2Q X) = ⊥ := pCore_two_quotient_eq_bot
  have hΩQ : Ω ≤ CFSG.pCore 2 (O2Q X) := le_sSup ⟨hΩn, hΩ2⟩
  rw [hO] at hΩQ
  refine ⟨fun c₁ hc₁ c₂ hc₂ => ?_, fun a ha ha2 => ?_⟩
  · have h1 := hab (π ⟨c₁, hCX hc₁⟩) ⟨⟨c₁, hCX hc₁⟩, hc₁, rfl⟩ (π ⟨c₂, hCX hc₂⟩)
      ⟨⟨c₂, hCX hc₂⟩, hc₂, rfl⟩
    have h3 : π (⟨c₁, hCX hc₁⟩ * ⟨c₂, hCX hc₂⟩ * ⟨c₁, hCX hc₁⟩⁻¹ * ⟨c₂, hCX hc₂⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv, h1, mul_inv_cancel_right, mul_inv_cancel]
    exact (hker _).mp h3
  · have hmem : π ⟨a, hCX ha⟩ ∈ Ω := ⟨⟨⟨a, hCX ha⟩, ha, rfl⟩, by
      rw [← map_pow, show (⟨a, hCX ha⟩ : ↥X) ^ 2 = 1 from Subtype.ext ha2, map_one]⟩
    have h3 := hΩQ hmem
    rw [Subgroup.mem_bot] at h3
    exact (hker _).mp h3

theorem omegaOneCenterOf_thompsonJk_le {Γ : Type} [Group Γ] [Finite Γ] {X P A : Subgroup Γ}
    {j : ℕ} (hchar : CharTwo X) (hPX : P ≤ X) (hQP : pCoreOf 2 X ≤ P)
    (hA : IsMaxElemAbelian P A) (hA₁ : A ⊓ pCoreOf 2 X ∈ E5.wFam j P (pCoreOf 2 X)) :
    omegaOneCenterOf (H13.thompsonJk j P) ≤ omegaOneCenterOf (E5.wGen j P (pCoreOf 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 X with hQdef
  set D := omegaOneCenterOf (H13.thompsonJk j P) with hDdef
  set W := E5.wGen j P Q with hWdef
  have hXQ : X ≤ Subgroup.normalizer (Q : Set Γ) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hA₁W : A ⊓ Q ≤ W := E5.le_wGen hA₁
  have hWQ : W ≤ Q := E5.wGen_le j P Q
  have hWJ : W ≤ H13.thompsonJk j P := E5.wGen_le_thompsonJk hQP
  have hXW : X ≤ Subgroup.normalizer (W : Set Γ) := E5.le_normalizer_wGen j hXQ
  have hDA : D ≤ A := E5.omegaOneCenterOf_le_of_isMaxElemAbelian hA
  have hDX : D ≤ X := hDA.trans (hA.1.trans hPX)
  have hDel : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hDW : D ≤ Subgroup.centralizer (W : Set Γ) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun w hw => mem_centralizer_of_mem_omegaOneCenterOf hd (hWJ hw)
  set S := X ⊓ Subgroup.centralizer (W : Set Γ) ⊓ E5.quotStab Q W with hSdef
  have hSX : S ≤ X := inf_le_left.trans inf_le_left
  have hXS : X ≤ Subgroup.normalizer (S : Set Γ) := by
    have key : ∀ k ∈ X, ∀ x ∈ S, k * x * k⁻¹ ∈ S := by
      intro k hk x ⟨⟨hxK, hxC⟩, hxN, hxS⟩
      refine ⟨⟨X.mul_mem (X.mul_mem hk hxK) (X.inv_mem hk), ?_⟩, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (E5.mem_normalizer_centralizer (hXW hk)) x).1 hxC
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXW hk) hxN) (Subgroup.inv_mem _ (hXW hk))
      · intro q hq
        have hq' : k⁻¹ * q * k⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.1 (hXQ (X.inv_mem hk)) q).1 hq
        have e : ⁅k * x * k⁻¹, q⁆ = k * ⁅x, k⁻¹ * q * k⁻¹⁻¹⁆ * k⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hXW hk) _).1 (hxS _ hq')
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have := key k⁻¹ (X.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hDS : D ≤ S := by
    intro d hd
    refine ⟨⟨hDX hd, hDW hd⟩, hXW (hDX hd), fun q hq => ?_⟩
    have hQD : q ∈ Subgroup.normalizer (D : Set Γ) :=
      normalizer_le_normalizer_omegaOneCenterOf _ (E5.le_normalizer_thompsonJk j P (hQP hq))
    have h1 : ⁅d, q⁆ ∈ D := by
      have : q * d⁻¹ * q⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hQD _).1 (D.inv_mem hd)
      have e : ⁅d, q⁆ = d * (q * d⁻¹ * q⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem hd this
    have h2 : ⁅d, q⁆ ∈ Q := by
      have : d * q * d⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hXQ (hDX hd)) q).1 hq
      have e : ⁅d, q⁆ = (d * q * d⁻¹) * q⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Q.mul_mem this (Q.inv_mem hq)
    exact hA₁W ⟨hDA h1, h2⟩
  have hS2 : IsPGroup 2 S := by
    intro s
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (s : Γ)).ne'
    have hyS : (s : Γ) ^ 2 ^ k ∈ S := S.pow_mem s.2 _
    have hord : orderOf ((s : Γ) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hkm ▸ dvd_mul_right _ _), hkm,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hyC := E5.mem_centralizer_of_odd hWQ hQ2 hyS.1.2 hyS.2 (hord ▸ hm)
    have hyQ : (s : Γ) ^ 2 ^ k ∈ Q := hchar ⟨hSX hyS, hyC⟩
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hQ2) ⟨_, hyQ⟩
    rw [Subgroup.orderOf_mk, hord] at ha
    have hm1 : m = 1 := by
      rcases a with _ | a
      · simpa using ha
      · exfalso
        rw [pow_succ] at ha
        exact (Nat.not_even_iff_odd.mpr hm) ⟨2 ^ a, by omega⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (s : Γ) ^ 2 ^ k = 1 := by
      rw [← orderOf_eq_one_iff, hord, hm1]
    simpa using h1
  have hSQ : S ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSX hXS hS2
  intro d hd
  exact mem_omegaOneCenterOf (hA₁W ⟨hDA hd, hSQ (hDS hd)⟩)
    (fun w hw => Subgroup.mem_centralizer_iff.mp (hDW hd) w hw) (hDel.2 d hd)

theorem card_le_two_pow_mul_card_inf {Γ : Type} [Group Γ] [Finite Γ] {X A : Subgroup Γ} {j : ℕ}
    (hAX : A ≤ X) (hA : IsElemAbelian 2 A)
    (hrank : CFSG.Open.pRank 2 (⊤ : Subgroup (O2Q X)) ≤ j) :
    Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ pCoreOf 2 X) := by
  set Q := pCoreOf 2 X with hQdef
  set π : ↥X →* O2Q X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπdef
  have hA' : IsElemAbelian 2 (A.subgroupOf X) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (B2F.isElemAbelian_comm hA
      (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩,
      fun a ha => Subtype.ext (hA.2 _ (Subgroup.mem_subgroupOf.mp ha))⟩
  have hAm : IsElemAbelian 2 ((A.subgroupOf X).map π) := E1.isElemAbelian_map' π hA'
  have hmap : Nat.card ↥((A.subgroupOf X).map π) ≤ 2 ^ j :=
    (card_le_two_pow_pRank_of_le le_top hAm).trans (Nat.pow_le_pow_right (by norm_num) hrank)
  have hker : π.ker = Q.subgroupOf X := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact mk_pCore_eq_one_iff X y
  have h1 : Q.relIndex A = Nat.card ↥((A.subgroupOf X).map π) := by
    rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hAX]
  have h3 := Subgroup.relIndex_mul_card Q A
  rw [inf_comm] at h3
  calc Nat.card A = Q.relIndex A * Nat.card ↥(A ⊓ Q) := h3.symm
    _ ≤ 2 ^ j * Nat.card ↥(A ⊓ Q) := Nat.mul_le_mul_right _ (by rw [h1]; exact hmap)

theorem false_of_section {Γ : Type} [Group Γ] [Finite Γ] {X P A E E' : Subgroup Γ}
    (hP : IsSylowTwoOf P X)
    (hqs : CFSG.IsQuasisimple ↥(CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X))))
    (h2 : ∀ q : O2Q X, ∃ e : ℕ, q ^ 2 ^ e ∈ CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X)))
    (hFF : ∀ Y : Subgroup Γ, (Y.subgroupOf X).Normal → pCoreOf 2 X ≤ Y → Y ≤ solvRad X →
      HasNoFaithfulFFModulesMod X Y)
    (hA : IsMaxElemAbelian P A) (hAQ : ¬ A ≤ pCoreOf 2 X) (hE : IsElemAbelian 2 E)
    (hEQ : E ≤ pCoreOf 2 X)
    (hbound : (A ⊓ pCoreOf 2 X).relIndex E ≤ (A ⊓ pCoreOf 2 X).relIndex A)
    (hE'E : E' ≤ E) (hXE' : X ≤ Subgroup.normalizer (E' : Set Γ))
    (hXF : X ≤ Subgroup.normalizer ((⁅E', pCoreOf 2 X⁆ : Subgroup Γ) : Set Γ)) {x : Γ}
    (hxX : x ∈ X) (hodd : Odd (orderOf x)) {e : Γ} (he : e ∈ E')
    (hxe : x * e * x⁻¹ * e⁻¹ ∉ ⁅E', pCoreOf 2 X⁆) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 X with hQdef
  set F := ⁅E', Q⁆ with hFdef
  have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set Γ) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hAX : A ≤ X := hA.1.trans hP.1
  have hE'X : E' ≤ X := (hE'E.trans hEQ).trans hQX
  have hE'F : E' ≤ Subgroup.normalizer (F : Set Γ) := hE'X.trans hXF
  have hE'el : IsElemAbelian 2 E' := B2F.isElemAbelian_mono hE'E hE
  have hsec : IsElemAbelian 2 (secImg (Subgroup.normalizer (F : Set Γ)) F E') := by
    refine isElemAbelian_secImg_normalizer (fun a ha b hb => ?_) (fun a ha => ?_)
    · have e1 : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [B2F.isElemAbelian_comm hE'el ha hb]
        group
      rw [e1]
      exact F.one_mem
    · rw [hE'el.2 a ha]
      exact F.one_mem
  set C := centralizerMod F X E' with hCdef
  have hCX : C ≤ X := centralizerMod_le_left F X E'
  have hXC : X ≤ Subgroup.normalizer (C : Set Γ) :=
    le_normalizer_centralizerMod hXF Subgroup.le_normalizer hXE'
  have hQC : Q ≤ C := by
    intro q hq
    refine ⟨hQX hq, hXF (hQX hq), fun u hu => ?_⟩
    have h1 : ⁅u, q⁆ ∈ F := Subgroup.commutator_mem_commutator hu hq
    have h3 := F.inv_mem h1
    have e1 : ⁅u, q⁆⁻¹ = q * u * q⁻¹ * u⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e1] at h3
  have hxC : x ∉ C := fun h => hxe (h.2.2 e he)
  obtain ⟨hcomm, hsq⟩ := commutator_mem_and_sq_mem hqs h2 hQC hCX hXC hxX hodd hxC
  have hAC : ∀ a ∈ A, a ∈ C → a ∈ Q := fun a ha haC => hsq a haC (hA.2.1.2 a ha)
  have hCsolv : Group.IsSolvable ↥C := by
    let Q' : Subgroup ↥C := Q.subgroupOf C
    have hQ'n : Q'.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).2 (hCX.trans hXQ)
    have hQ'2 : IsPGroup 2 ↥Q' := hQ2.comap_of_injective C.subtype C.subtype_injective
    have : Group.IsSolvable ↥Q' := E1.isSolvable_of_isPGroup_two hQ'2
    have : Group.IsSolvable (↥C ⧸ Q') := by
      refine Group.isSolvable_of_comm fun a b => ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h := hcomm _ (C.inv_mem b.2) _ (C.inv_mem a.2)
      simpa [mul_assoc] using h
    exact Group.isSolvable_of_subgroup_quotient Q'
  have hCn : (C.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).2 hXC
  have hNo := hFF C hCn hQC (le_solvRad hCX hCn hCsolv)
  refine not_hasNoFaithfulFFModulesMod_of_isFFInt (C := C) hXF hXE' hE'F hsec
    (fun y hy u hu => hy.2.2.2 u hu) (fun y hy h => ⟨hy, hXF hy, h⟩) ?_ hNo
  refine isFFModule_autOn_secImg hsec hE'F hXF hXE' hAX hA.2.1 ?_ ?_
  · intro hall
    exact hAQ fun a ha => hAC a ha ⟨hAX ha, hXF (hAX ha), hall a ha⟩
  · have h1 : E' ⊓ (A ⊓ Q) ≤ centralizerMod F E' A := by
      intro y hy
      refine ⟨hy.1, hE'F hy.1, fun a ha => ?_⟩
      have e1 : y * a * y⁻¹ * a⁻¹ = 1 := by
        rw [B2F.isElemAbelian_comm hA.2.1 hy.2.1 ha]
        group
      rw [e1]
      exact F.one_mem
    have h3 : centralizerMod F A E' ≤ A ⊓ Q := fun a ha =>
      ⟨ha.1, hAC a ha.1 ⟨hAX ha.1, ha.2.1, ha.2.2⟩⟩
    calc (centralizerMod F E' A).relIndex E' ≤ (E' ⊓ (A ⊓ Q)).relIndex E' :=
          Subgroup.relIndex_le_of_le_left h1 (E3.relIndex_ne_zero' _ _)
      _ = (A ⊓ Q).relIndex E' := Subgroup.inf_relIndex_left _ _
      _ ≤ (A ⊓ Q).relIndex E := Subgroup.relIndex_le_of_le_right hE'E (E3.relIndex_ne_zero' _ _)
      _ ≤ (A ⊓ Q).relIndex A := hbound
      _ ≤ (centralizerMod F A E').relIndex A :=
          Subgroup.relIndex_le_of_le_left h3 (E3.relIndex_ne_zero' _ _)

end E54

open E54 in
theorem AS_I_E_5_4'_holds :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X P : Subgroup Γ) (j : ℕ), 0 < j → IsSylowTwoOf P X →
      CharTwo X → CFSG.IsQuasisimple ↥(CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X))) →
      (∀ q : O2Q X, ∃ e : ℕ, q ^ 2 ^ e ∈ CFSG.Open.quasithinGenFitting (⊤ : Subgroup (O2Q X))) →
      CFSG.Open.pRank 2 (⊤ : Subgroup (O2Q X)) ≤ j →
      (∀ Y : Subgroup Γ, (Y.subgroupOf X).Normal → pCoreOf 2 X ≤ Y → Y ≤ solvRad X →
        HasNoFaithfulFFModulesMod X Y) →
        X ≤ Subgroup.normalizer (thompsonJ P : Set Γ) ∨
          (oTwoUpper X ≤ Subgroup.centralizer
              (CFSG.Quasithin.omegaOneCenterOf (thompsonJi P j) : Set Γ) ∧
            X ≤ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf (thompsonJi P j) : Set Γ)) := by
  intro Γ _ _ X P j _hj hP hchar hqs h2 hrank hFF
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 X with hQdef
  have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set Γ) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hQP : Q ≤ P := A4.le_of_normal_of_isSylowTwoOf hP hQX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQX).2 hXQ) hQ2
  by_cases hJQ : thompsonJ P ≤ Q
  · left
    have hJ : thompsonJ P = thompsonJ Q := CFSG.Quasithin.thompsonJ_eq_of_le hJQ hQP
    intro g hg
    rw [hJ]
    exact E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ (hXQ hg))
  right
  obtain ⟨A, hA, hAQ⟩ : ∃ A, IsMaxElemAbelian P A ∧ ¬ A ≤ Q := by
    by_contra h
    push Not at h
    exact hJQ (iSup₂_le fun A hA => h A hA)
  rcases le_or_gt (CFSG.Open.pRank 2 P) j with hjm | hjm
  ·
    rw [thompsonJi_eq_bot_of_le hjm, omegaOneCenterOf_bot_eq]
    refine ⟨fun y _ => ?_, fun y _ => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
    · rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top y
  rw [thompsonJi_eq_thompsonJk hjm]
  have hAX : A ≤ X := hA.1.trans hP.1
  have hR := card_le_two_pow_mul_card_inf hAX hA.2.1 hrank
  have hA₁ : A ⊓ Q ∈ E5.wFam j P Q :=
    ⟨inf_le_right, B2F.isElemAbelian_mono inf_le_left hA.2.1,
      fun B hBP hB => (hA.2.2 B hBP hB).trans hR⟩
  have hDE := omegaOneCenterOf_thompsonJk_le hchar hP.1 hQP hA hA₁
  set W := E5.wGen j P Q with hWdef
  set E := omegaOneCenterOf W with hEdef
  have hA₁W : A ⊓ Q ≤ W := E5.le_wGen hA₁
  have hWQ : W ≤ Q := E5.wGen_le j P Q
  have hXW : X ≤ Subgroup.normalizer (W : Set Γ) := E5.le_normalizer_wGen j hXQ
  have hXE : X ≤ Subgroup.normalizer (E : Set Γ) :=
    hXW.trans (normalizer_le_normalizer_omegaOneCenterOf W)
  have hEel : IsElemAbelian 2 E := B2F.isElemAbelian_omegaOneCenterOf W
  have hEQ : E ≤ Q := (omegaOneCenterOf_le W).trans hWQ
  have hbound : (A ⊓ Q).relIndex E ≤ (A ⊓ Q).relIndex A := by
    have hEA₁ : IsElemAbelian 2 (E ⊔ (A ⊓ Q)) :=
      B2F.isElemAbelian_sup_of_commute hEel hA₁.2.1 fun e he a ha =>
        (mem_centralizer_of_mem_omegaOneCenterOf he (hA₁W ha)).symm
    have hEA₁P : E ⊔ (A ⊓ Q) ≤ P := sup_le (hEQ.trans hQP) (inf_le_left.trans hA.1)
    have hcard := hA.2.2 _ hEA₁P hEA₁
    have h3 := Subgroup.relIndex_mul_card (A ⊓ Q) (E ⊔ (A ⊓ Q))
    have e3 : A ⊓ Q ⊓ (E ⊔ (A ⊓ Q)) = A ⊓ Q := inf_eq_left.2 le_sup_right
    rw [e3] at h3
    have h4 := Subgroup.relIndex_mul_card (A ⊓ Q) A
    have e4 : A ⊓ Q ⊓ A = A ⊓ Q := inf_eq_left.2 inf_le_left
    rw [e4] at h4
    have h5 : (A ⊓ Q).relIndex (E ⊔ (A ⊓ Q)) ≤ (A ⊓ Q).relIndex A := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := ↥(A ⊓ Q)))
      rw [h3, h4]
      exact hcard
    exact (Subgroup.relIndex_le_of_le_right le_sup_left (E3.relIndex_ne_zero' _ _)).trans h5
  have hOE : oTwoUpper X ≤ Subgroup.centralizer (E : Set Γ) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    by_contra hxE
    obtain ⟨E', hE'E, hXE', hXF, e, he, hxe⟩ :=
      exists_section_of_odd hQ2 hEQ hQX hXQ hXE hx.1 hx.2 hxE
    exact false_of_section hP hqs h2 hFF hA hAQ hEel hEQ hbound hE'E hXE' hXF hx.1 hx.2 he hxe
  set D := omegaOneCenterOf (H13.thompsonJk j P) with hDdef
  have hOD : oTwoUpper X ≤ Subgroup.centralizer (D : Set Γ) :=
    hOE.trans (Subgroup.centralizer_le hDE)
  have hPD : P ≤ Subgroup.normalizer (D : Set Γ) :=
    (E5.le_normalizer_thompsonJk j P).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  refine ⟨hOD, ?_⟩
  have hres : twoResidual X ≤ oTwoUpper X :=
    twoResidual_le_of_isTwoQuotient (oTwoUpper_le X) (le_normalizer_oTwoUpper X)
      fun y hy => exists_pow_mem_oTwoUpper X hy
  exact (sup_twoResidual_eq hP).ge.trans
    (sup_le hPD ((hres.trans hOD).trans (Subgroup.centralizer_le_normalizer _)))

end CFSG.Quasithin.VolI
