module

public import CFSG.Quasithin.Background.C31SporPull
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.Vol2.Ch11SecOE2D
public import CFSG.Quasithin.Background.SmithB42U33SixProof
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import CFSG.Quasithin.Vol2.KGFactC31Gen
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31Rad

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint Matrix
  CFSG.LieType.BorelTits

variable {A : Type} [Group A]

theorem concl_L3 [Finite A] {G₀ : Type} [Group G₀] [Finite G₀] {S M₀ R M V : Subgroup A}
    (hSs : IsSporadic .Ru ↥S) (hcS : Subgroup.center ↥S = ⊥) (hM₀S : M₀ ≤ S)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hcomm : ⁅V, M₀⁆ = V) (ι : G₀ →* A)
    (hι : Function.Injective ι) {v : Fin 3 → G₀} (hv : EBasis v) {K N : Subgroup G₀}
    (hKN : K ≤ N) (hcN : Nat.card N = 168 * Nat.card K) (hK : IsSpecial2Group 3 8 ↥K)
    (hNC : ∀ x ∈ N, x ∈ Subgroup.centralizer (eSub hv : Set G₀) ↔ x ∈ K)
    (hV : V = (eSub hv).map ι) (hO : pCoreOf 2 M₀ = K.map ι) (hM : M₀ = N.map ι)
    (hR : R = Subgroup.centralizer (((eSub hv).map ι : Subgroup A) : Set A)) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (v i) := hv.map hι
  have hVA : (eSub hv).map ι = eSub hvA := eSub_map hv hι
  have hcent : ∀ x ∈ M₀, x ∈ Subgroup.centralizer (V : Set A) ↔ x ∈ K.map ι := by
    intro x hx
    rw [hM] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [hV, Subgroup.mem_map_iff_mem hι, ← hNC n hn, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h e he
      exact hι (by simpa using h (ι e) ⟨e, he, rfl⟩)
    · rintro h _ ⟨e, he, rfl⟩
      rw [← map_mul, ← map_mul, h e he]
  rw [hVA] at hV hR
  subst hV
  set V := eSub hvA with hVdef
  have hM₀N : M₀ ≤ eNorm hvA := le_normalizer_of_comm hcomm
  have hRC : R ≤ Subgroup.centralizer (V : Set A) := hR.le
  have hRN' : R ≤ eNorm hvA := fun r hr => mem_eNorm_of_cent hvA (hRC hr)
  have hXN : M₀ ⊔ R ≤ eNorm hvA := sup_le hM₀N hRN'
  have hKle : K.map ι ≤ M₀ := hM ▸ Subgroup.map_mono hKN
  let α₀ := E8.e3Hom hvA hM₀N
  have hker₀ : α₀.ker = (K.map ι).subgroupOf M₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
    exact hcent x x.2
  have hcM : Nat.card M₀ = 168 * Nat.card K := by
    rw [hM, Subgroup.card_map_of_injective hι, hcN]
  have hsurj₀ : Function.Surjective α₀ := by
    have h1 := card_range_eq hKle α₀ hker₀
    rw [Subgroup.card_map_of_injective hι, hcM] at h1
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card α₀.range = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
      rw [E8.card_statedSL3]
      exact Nat.eq_of_mul_eq_mul_right hKpos h1
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hpk : CFSG.pCore 2 ↥M₀ = α₀.ker := by rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  have hpsl : IsPSL 3 2 1 (ModO2 M₀) := E8.isPSL_of_equiv3
    ((QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))
  have hext : IsExt ↥M₀ (fun N _ => IsSpecial2Group 3 8 N) (fun Y _ => IsPSL 3 2 1 Y) := by
    have hn : ((K.map ι).subgroupOf M₀).Normal := by rw [← hker₀]; exact α₀.normal_ker
    refine ⟨(K.map ι).subgroupOf M₀, hn, ?_, E8.isPSL_of_equiv3
      ((QuotientGroup.quotientMulEquivOfEq hker₀.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀))⟩
    exact C31Spor.isSpecial2Group_of_mulEquiv
      ((K.equivMapOfInjective ι hι).trans (Subgroup.subgroupOfEquivOfLe hKle).symm) hK
  have hXC : (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R :=
    le_antisymm (inf_le_right.trans hR.symm.le) (le_inf le_sup_right hRC)
  let α := E8.e3Hom hvA hXN
  have hker : α.ker = R.subgroupOf (M₀ ⊔ R) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
    constructor
    · intro h
      have h3 : (x : A) ∈ (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) := ⟨x.2, h⟩
      rw [hXC] at h3
      exact h3
    · intro hx; exact hRC hx
  have hsurj : Function.Surjective α := by
    intro σ
    obtain ⟨m, hm⟩ := hsurj₀ σ
    exact ⟨⟨m, le_sup_left (a := M₀) m.2⟩, Subtype.ext (Units.ext (by
      rw [← hm]; rfl))⟩
  let β : ↥V →* Multiplicative (Fin 3 → ZMod 2) := (ecoords hvA).toMonoidHom
  have hsec : IsNaturalSection (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
      (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
    refine ⟨hXN, α, hsurj, hker, β, (ecoords hvA).surjective, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr (ecoords hvA).injective
    · intro a u w hw
      exact ecoords_conj hvA ⟨a, hXN a.2⟩ u w hw
  have hsum : IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R))
      (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' hMN
  have hsp := isSporadic_quot_center hcS hSs
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hsp, Or.inl ?_⟩))))),
    Or.inr (Or.inl ⟨3, Or.inl rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm
      (fun _ _ _ _ e h => C31Spor.isSpecial2Group_of_mulEquiv e h) (isPSL_of_mulEquiv 3 2 1) hext
  · refine summand_of_card ?_
    rw [card_eSub]
    norm_num

theorem isQuasisimple_of_isPSU33 {X : Type} [Group X] (h : IsPSU 3 3 1 X) :
    CFSG.IsQuasisimple X := by
  have hs : IsSimpleGroup X := SBc11.isSimpleGroup_of_list (Or.inr (Or.inr h))
  have := hs
  have hc : Nat.card X = 6048 := SBc11.card_of_isPSU_three_three h
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [hc]; norm_num)
    have hn : (Subgroup.zpowers g).Normal := ⟨fun x hx y => by
      rw [hall y x, mul_inv_cancel_right]; exact hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h | h
    · have : g = 1 := by
        have := Subgroup.mem_zpowers g
        rwa [h, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hg
      norm_num at hg
    · have h2 := Nat.card_zpowers g
      rw [h, Subgroup.card_top, hc, hg] at h2
      norm_num at h2
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hperf : Group.IsPerfect X := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have : a * b * a⁻¹ * b⁻¹ ∈ commutator X := by
        rw [← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at this
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [this, one_mul]
    · exact h
  have e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

variable {Γ : Type} [Group Γ]

private theorem isG2BlockNumeric_aux [Finite Γ] {L Q : Subgroup Γ} [(Q.subgroupOf L).Normal]
    (hQ : IsElemAbelian 2 Q) (hLN : L ≤ Subgroup.normalizer (Q : Set Γ)) (hO : pCoreOf 2 L = Q)
    (hcard : Nat.card Q = 64)
    (hC : L ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q) (hperf : ⁅L, L⁆ = L)
    (hpsu : IsPSU 3 3 1 (↥L ⧸ Q.subgroupOf L)) {t : Γ}
    (htrans : ∀ u ∈ Q, u ≠ 1 → ∃ l ∈ L, l * t * l⁻¹ = u) :
    CFSG.QuasithinUnique.IsShort2 L ∧
      IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      ((CFSG.QuasithinUnique.blockZ L).subgroupOf
        (CFSG.QuasithinUnique.blockU L)).index = 2 ^ 6 ∧
      CFSG.QuasithinUnique.blockU L = Q ∧ CFSG.QuasithinUnique.blockZ L = ⊥ := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  have hQC : Q ≤ Subgroup.centralizer (Q : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hQab y hy x hx
  have hirr : ∀ W : Subgroup Γ, W ≤ Q → L ≤ Subgroup.normalizer (W : Set Γ) → W = ⊥ ∨ W = Q := by
    intro W hWQ hLW
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      obtain ⟨⟨w, hw⟩, hw1⟩ := W.ne_bot_iff_exists_ne_one.mp hW
      have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
      obtain ⟨l, hl, hlw⟩ := htrans w (hWQ hw) hw1'
      have htW : t ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (hLW (L.inv_mem hl)) w).mp hw
        rwa [← hlw, show l⁻¹ * (l * t * l⁻¹) * l⁻¹⁻¹ = t by group] at this
      refine le_antisymm hWQ fun u hu => ?_
      by_cases hu1 : u = 1
      · rw [hu1]; exact W.one_mem
      · obtain ⟨l', hl', rfl⟩ := htrans u hu hu1
        exact (Subgroup.mem_normalizer_iff.mp (hLW hl') t).mp htW
  have hLnorm : L ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (L : Set Γ) : Subgroup Γ) : Set Γ) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hLN hl) x).mp hxQ,
        Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      have h2 := Subgroup.mem_centralizer_iff.mp hxC (l⁻¹ * m * l)
        (L.mul_mem (L.mul_mem (L.inv_mem hl) hm) hl)
      calc m * (l * x * l⁻¹) = l * ((l⁻¹ * m * l) * x) * l⁻¹ := by group
        _ = l * (x * (l⁻¹ * m * l)) * l⁻¹ := by rw [h2]
        _ = l * x * l⁻¹ * m := by group
    · rintro ⟨hxQ, hxC⟩
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hLN (L.inv_mem hl)) (l * x * l⁻¹)).mp hxQ
        rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at this
      · have h1 := Subgroup.mem_centralizer_iff.mp hxC (l * m * l⁻¹)
          (L.mul_mem (L.mul_mem hl hm) (L.inv_mem hl))
        have e1 : l * m * l⁻¹ * (l * x * l⁻¹) = l * (m * x) * l⁻¹ := by group
        have e2 : l * x * l⁻¹ * (l * m * l⁻¹) = l * (x * m) * l⁻¹ := by group
        rw [e1, e2] at h1
        exact mul_left_cancel (mul_right_cancel h1)
  have hinf : Q ⊓ Subgroup.centralizer (L : Set Γ) = ⊥ := by
    rcases hirr (Q ⊓ Subgroup.centralizer (L : Set Γ)) inf_le_left hLnorm with h | h
    · exact h
    · exfalso
      have hLQ : L ≤ Q := fun l hl => hC ⟨hl, Subgroup.mem_centralizer_iff.mpr fun q hq => by
        have hq' : q ∈ Q ⊓ Subgroup.centralizer (L : Set Γ) := by rw [h]; exact hq
        exact (Subgroup.mem_centralizer_iff.mp hq'.2 l hl).symm⟩
      have hc6 := SBc11.card_of_isPSU_three_three hpsu
      have h1 : Nat.card (↥L ⧸ Q.subgroupOf L) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun x y => ?_⟩, inferInstance⟩
        induction x using QuotientGroup.induction_on with
        | H a =>
          induction y using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
            exact hLQ (L.mul_mem (L.inv_mem a.2) b.2)
      rw [h1] at hc6
      norm_num at hc6
  have hcommle : ⁅Q, L⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    rw [commutatorElement_def]
    have h1 : l * q⁻¹ * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp (Q.inv_mem hq)
    have := Q.mul_mem hq h1
    rwa [show q * (l * q⁻¹ * l⁻¹) = q * l * q⁻¹ * l⁻¹ by group] at this
  have hcommN : L ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := Q) (H₂ := L)
  have hU : ⁅Q, L⁆ = Q := by
    rcases hirr _ hcommle hcommN with h | h
    · exfalso
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have hQ' : Q ≤ Q ⊓ Subgroup.centralizer (L : Set Γ) := le_inf le_rfl h
      rw [hinf, le_bot_iff] at hQ'
      rw [hQ', Subgroup.card_bot] at hcard
      norm_num at hcard
    · exact h
  have hbQ : CFSG.QuasithinUnique.blockQ L = Q := hO
  have hbU : CFSG.QuasithinUnique.blockU L = Q := by
    rw [CFSG.QuasithinUnique.blockU, hbQ, hU]
  have hbZ : CFSG.QuasithinUnique.blockZ L = ⊥ := by
    rw [CFSG.QuasithinUnique.blockZ, hbU, hinf]
  have hpk : CFSG.pCore 2 ↥L = Q.subgroupOf L := by rw [← Hex.pCoreOf_subgroupOf' L, hO]
  have hpsuP : IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    C31Spor.isPSU_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpk).symm hpsu
  have hpL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hshort : CFSG.QuasithinUnique.IsShort2 L := by
    refine ⟨fun N _ hN => Hex.eq_top_of_isPGroup_quot' N hN, ?_, ⟨?_, ?_⟩,
      Or.inl (isQuasisimple_of_isPSU33 hpsuP), ?_, ?_⟩
    · unfold CFSG.QuasithinUnique.CharTwo
      rw [hO]
      exact hC
    · rw [hbU, hbQ]
      exact le_inf le_rfl hQC
    · intro x hx
      rw [hbU] at hx
      exact hQ.2 x hx
    · rw [hbZ, hbU]
      exact bot_lt_iff_ne_bot.mpr hQne
    · intro W hZW hWU hLW
      rw [hbZ, hbU] at *
      exact hirr W hWU hLW
  refine ⟨hshort, hpsuP, ?_, hbU, hbZ⟩
  rw [hbZ, hbU, Subgroup.bot_subgroupOf, Subgroup.index_bot, hcard]
  norm_num

open scoped IsMulCommutative in
theorem isG2Block_of [Finite Γ] {L Q : Subgroup Γ} [(Q.subgroupOf L).Normal]
    (hQ : IsElemAbelian 2 Q) (hLN : L ≤ Subgroup.normalizer (Q : Set Γ)) (hO : pCoreOf 2 L = Q)
    (hcard : Nat.card Q = 64)
    (hC : L ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q) (hperf : ⁅L, L⁆ = L)
    (hpsu : IsPSU 3 3 1 (↥L ⧸ Q.subgroupOf L)) {t : Γ}
    (htrans : ∀ u ∈ Q, u ≠ 1 → ∃ l ∈ L, l * t * l⁻¹ = u) :
    CFSG.Quasithin.IsG2Block L := by
  obtain ⟨short, quotient, -, hbU, hbZ⟩ :=
    isG2BlockNumeric_aux hQ hLN hO hcard hC hperf hpsu htrans
  have hpk : CFSG.pCore 2 ↥L = Q.subgroupOf L := by rw [← Hex.pCoreOf_subgroupOf' L, hO]
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  have hLU : L ≤ Subgroup.normalizer (CFSG.QuasithinUnique.blockU L : Set Γ) := by
    rw [hbU]
    exact hLN
  let c : ↥L →* ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) :=
    ((CFSG.Quasithin.conjAct (CFSG.QuasithinUnique.blockU L)).comp
      (Subgroup.inclusion hLU)).codRestrict _
      (fun ℓ => ⟨⟨ℓ, hLU ℓ.2⟩, Subgroup.mem_subgroupOf.mpr ℓ.2, rfl⟩)
  have c_apply : ∀ (ℓ : ↥L) (u : ↥(CFSG.QuasithinUnique.blockU L)),
      ((((c ℓ : ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L))) :
        MulAut ↥(CFSG.QuasithinUnique.blockU L)) u : ↥(CFSG.QuasithinUnique.blockU L)) : Γ) =
        (ℓ : Γ) * (u : Γ) * (ℓ : Γ)⁻¹ := fun _ _ => rfl
  have hcsurj : Function.Surjective c := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp hφ
    exact ⟨⟨(x : Γ), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxφ⟩
  have hc_one : ∀ ℓ : ↥L, c ℓ = 1 ↔
      ∀ u : ↥(CFSG.QuasithinUnique.blockU L), (ℓ : Γ) * (u : Γ) * (ℓ : Γ)⁻¹ = (u : Γ) := by
    intro ℓ
    constructor
    · intro h u
      have h1 := congrArg (fun φ : ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) =>
        ((φ : MulAut ↥(CFSG.QuasithinUnique.blockU L)) u : Γ)) h
      simpa [c_apply] using h1
    · intro h
      apply Subtype.ext
      rw [Subgroup.coe_one]
      apply MulEquiv.ext
      intro u
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [c_apply]
      exact h u
  have hker : c.ker = CFSG.pCore 2 ↥L := by
    rw [hpk]
    ext ℓ
    rw [MonoidHom.mem_ker, hc_one, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hcent : (ℓ : Γ) ∈ Subgroup.centralizer (Q : Set Γ) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hqU : q ∈ CFSG.QuasithinUnique.blockU L := by
          rw [hbU]
          exact hq
        have h2 : (ℓ : Γ) * q * (ℓ : Γ)⁻¹ = q := h ⟨q, hqU⟩
        exact (mul_inv_eq_iff_eq_mul.mp h2).symm
      exact hC (show (ℓ : Γ) ∈ L ⊓ Subgroup.centralizer (Q : Set Γ) from ⟨ℓ.2, hcent⟩)
    · intro hq u
      have huQ : (u : Γ) ∈ Q := by
        rw [← hbU]
        exact u.2
      rw [hQab _ hq _ huQ, mul_inv_cancel_right]
  let eQ : ↥L ⧸ c.ker ≃* ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) :=
    QuotientGroup.quotientKerEquivOfSurjective c hcsurj
  let eA : ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
    eQ.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)
  have hPA : IsPSU 3 3 1 ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) :=
    C31Spor.isPSU_of_mulEquiv eA.symm quotient
  have hZA : Subgroup.center ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) = ⊥ :=
    SBc11.center_eq_bot_of_list (Or.inr (Or.inr hPA))
  have hB42 : CFSG.Quasithin.B42TypeU33
      ↥(CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) := by
    unfold CFSG.Quasithin.B42TypeU33
    exact ⟨hZA, C31Spor.isPSU_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZA).trans QuotientGroup.quotientBot).symm hPA⟩
  obtain ⟨θ⟩ := CFSG.Quasithin.B42U33.nonempty_equiv_g2Derived hB42
  let jD : ↥(CFSG.Quasithin.H13.g2Derived (ZMod 2)) ≃*
      ↥⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆ :=
    Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)
  have hcomm : IsMulCommutative ↥(CFSG.QuasithinUnique.blockU L) := by
    rw [hbU]
    exact hQ.1
  have hexp : ∀ v : ↥(CFSG.QuasithinUnique.blockU L), v ^ 2 = 1 := fun v => by
    have hvQ : (v : Γ) ∈ Q := by
      rw [← hbU]
      exact v.2
    apply Subtype.ext
    simpa using hQ.2 _ hvQ
  have hcardV : Nat.card ↥(CFSG.QuasithinUnique.blockU L) = 2 ^ 6 := by
    rw [hbU, hcard]
    norm_num
  have hZ' : (CFSG.QuasithinUnique.blockZ L).subgroupOf (CFSG.QuasithinUnique.blockU L) = ⊥ := by
    rw [hbZ, Subgroup.bot_subgroupOf]
  have hG : CFSG.Quasithin.G2NaturalDerived (V := ↥(CFSG.QuasithinUnique.blockU L))
      (CFSG.Quasithin.autOn L (CFSG.QuasithinUnique.blockU L)) ⊤
      ((CFSG.QuasithinUnique.blockZ L).subgroupOf (CFSG.QuasithinUnique.blockU L)) 1 := by
    rw [hZ']
    exact CFSG.Quasithin.B42U33.u33SixNatural _ hexp hcardV _ hB42
  have h13 : CFSG.Quasithin.H13.IsG2Block L :=
    ⟨short, ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
      ⟨eA.symm.trans (θ.trans jD)⟩⟩, hcomm, hG⟩
  exact CFSG.Quasithin.Vol2.Ch11.OE2.isG2Block_of h13

theorem concl_G2 [Finite A] {G₀ : Type} [Group G₀] [Finite G₀] {S M₀ R M V : Subgroup A}
    (hSs : IsSporadic .Ru ↥S) (hcS : Subgroup.center ↥S = ⊥) (hM₀S : M₀ ≤ S)
    (hper : ⁅M₀, M₀⁆ = M₀) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hcomm : ⁅V, M₀⁆ = V)
    (ι : G₀ →* A) (hι : Function.Injective ι) {v : Fin 6 → G₀} (hv : EBasis v)
    {M' : Subgroup G₀} (hUM : eSub hv ≤ M') [((eSub hv).subgroupOf M').Normal]
    (hpsu : IsPSU 3 3 1 (↥M' ⧸ (eSub hv).subgroupOf M')) {t : G₀}
    (htrans : ∀ u ∈ eSub hv, u ≠ 1 → ∃ m ∈ M', m * t * m⁻¹ = u)
    (hV : V = (eSub hv).map ι) (hO : pCoreOf 2 M₀ = (eSub hv).map ι) (hM : M₀ = M'.map ι)
    (hC : M₀ ⊓ Subgroup.centralizer (V : Set A) ≤ V) :
    Concl S M₀ R M V := by
  have hvA : EBasis fun i => ι (v i) := hv.map hι
  have hVA : (eSub hv).map ι = eSub hvA := eSub_map hv hι
  have hVM : V ≤ M₀ := by rw [hV, hM]; exact Subgroup.map_mono hUM
  have hM₀N : M₀ ≤ Subgroup.normalizer (V : Set A) := le_normalizer_of_comm hcomm
  have hn : (V.subgroupOf M₀).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hM₀N g.2) x).mp hx
  have hVab : IsElemAbelian 2 V := by
    rw [hV, hVA]
    refine ⟨⟨⟨fun a b => Subtype.ext (eSub_comm hvA _ _ a.2 b.2)⟩⟩, fun x hx => ?_⟩
    rw [sq]; exact eSub_sq hvA x hx
  have hcard : Nat.card V = 64 := by rw [hV, hVA, card_eSub]; norm_num
  have hiso : (↥M' ⧸ (eSub hv).subgroupOf M') ≃* (↥M₀ ⧸ V.subgroupOf M₀) := by
    subst hM hV
    have he : ((eSub hv).subgroupOf M').map (M'.equivMapOfInjective ι hι).toMonoidHom =
        ((eSub hv).map ι).subgroupOf (M'.map ι) := by
      ext ⟨x, hx⟩
      rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨⟨y, hyM⟩, hy, hyx⟩
        rw [Subgroup.mem_subgroupOf] at hy
        exact ⟨y, hy, congrArg Subtype.val hyx⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hUM hy⟩, by rwa [Subgroup.mem_subgroupOf], rfl⟩
    exact QuotientGroup.congr _ _ (M'.equivMapOfInjective ι hι) he
  have hpsu' : IsPSU 3 3 1 (↥M₀ ⧸ V.subgroupOf M₀) := C31Spor.isPSU_of_mulEquiv hiso hpsu
  have htrans' : ∀ u ∈ V, u ≠ 1 → ∃ l ∈ M₀, l * ι t * l⁻¹ = u := by
    intro u hu hu1
    rw [hV] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨m, hm, hmu⟩ := htrans u' hu' (fun h => hu1 (by rw [h, map_one]))
    exact ⟨ι m, hM ▸ ⟨m, hm, rfl⟩, by rw [← hmu, map_mul, map_mul, map_inv]⟩
  have hO' : pCoreOf 2 M₀ = V := hO.trans hV.symm
  have hblock : IsG2Block M₀ := by
    have := hn
    exact isG2Block_of hVab hM₀N hO' hcard hC hper hpsu' htrans'
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' hMN
  have hsp := isSporadic_quot_center hcS hSs
  have hE6 : IsE2 6 ↥(V.subgroupOf M₀) := by
    have e1 : ↥(V.subgroupOf M₀) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVM
    have e2 : ↥V ≃* ↥(eSub hvA) := MulEquiv.subgroupCongr (hV.trans hVA)
    exact ⟨(e1.trans e2).trans (ecoords hvA)⟩
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hsp, Or.inr ?_⟩))))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hsp, hblock⟩))))), ?_⟩
  · rw [hM₀]
    exact isExt_of_mulEquiv (imageModCenterEquiv hM₀S hcS).symm (isE2_of_mulEquiv 6)
      (fun _ _ _ _ e h => C31Spor.isPSU_of_mulEquiv e h) ⟨V.subgroupOf M₀, hn, hE6, hpsu'⟩
  · exact summand_of_card64 hcard.le

end CFSG.Quasithin.KGC31

end
