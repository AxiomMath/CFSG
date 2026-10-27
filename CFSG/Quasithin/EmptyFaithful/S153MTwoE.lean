module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoK
public import CFSG.Quasithin.EmptyFaithful.S153MLayer
public import CFSG.Quasithin.EmptyFaithful.S1565M3
public import CFSG.Quasithin.EmptyFaithful.S1565M13

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565
open scoped Pointwise commutatorElement

namespace S153M

section Good

variable {V : Type} [CommGroup V]

theorem exists_good_pair {Hg : Type} [Group Hg] (ρ : Hg →* MulAut V) (K₁ : Subgroup Hg) (t : Hg)
    (hconcl : TwoActConcl ρ K₁ t) (S : Sylow 2 ↥(K₁.map ρ)) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥(K₁.map ρ)) : Set ↥(K₁.map ρ)), ∃ r : ℕ, Odd r ∧
      (((b : MulAut V) * (ρ t * (b : MulAut V) * (ρ t)⁻¹)) ^ r = 1) ∧
      ∀ w : V, (((b : MulAut V) * (ρ t * (b : MulAut V) * (ρ t)⁻¹)) w) * w⁻¹ ∈
          fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) →
        w ∈ fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) := by
  obtain ⟨-, ⟨⟨m, hm2, hnat⟩, -, -, -, hsum, hA, -⟩, hc, hn', hτ2, hconj⟩ := hconcl
  have hnat' : BinaryNaturalSL (K₁.map ρ)
      (commV (K₁.map ρ) ⊔ fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ))
      ((commV (K₁.map ρ) ⊔ fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ)) ⊓
        fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ)) 2 m := by
    rwa [inf_eq_right.mpr le_sup_right]
  obtain ⟨b, hbN, r, hr, hbr, hbfix⟩ := natfree_sl2_of_two_le hm2 hnat' S
  have hτX : ρ t ∈ ρ.range := ⟨t, rfl⟩
  have hτN : ρ t ∈ Subgroup.normalizer
      ((K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ : Subgroup (MulAut V)) :
        Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => hn' _ hτX l hl, fun hl => ?_⟩
    have := hn' (ρ t)⁻¹ ⟨t⁻¹, by simp⟩ _ hl
    simpa [mul_assoc] using this
  have hτ2' : ∀ g ∈ K₁.map ρ, (ρ t)⁻¹ * g * ρ t ∈ conjAutSub (ρ t) (K₁.map ρ) := by
    intro g hg
    have h1 := hτ2 g hg
    rw [conjAutSub, ← hconj]
    exact h1
  have hA' : commV (K₁.map ρ) ≤ fixV (conjAutSub (ρ t) (K₁.map ρ)) := by
    rw [conjAutSub, ← hconj]
    exact hA
  have hNat : ∀ a ∈ commV (K₁.map ρ), (b : MulAut V) a * a⁻¹ ∈
      commV (K₁.map ρ) ⊓ fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) →
      a ∈ fixV (K₁.map ρ ⊔ (K₁.map (MulAut.conj t).toMonoidHom).map ρ) := by
    intro a ha hh
    have := hbfix a (Subgroup.mem_sup_left ha) (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left
      (Subgroup.mem_inf.mp hh).1, (Subgroup.mem_inf.mp hh).2⟩)
    exact (Subgroup.mem_inf.mp this).2
  have hgood := mod_sum_good (le_sup_left) hτN hτ2' hsum hA' b.2 hNat
  refine ⟨b, hbN, r, hr, ?_, hgood⟩
  have hbr' : ((b : MulAut V)) ^ r = 1 := by
    have := congrArg Subtype.val hbr
    simpa using this
  have hcomm : Commute (b : MulAut V) (ρ t * (b : MulAut V) * (ρ t)⁻¹) := by
    refine hc (b : MulAut V) b.2 _ ?_
    rw [hconj]
    exact ⟨(b : MulAut V), b.2, by simp [MulAut.conj_apply]⟩
  rw [hcomm.mul_pow, hbr', conj_pow, hbr']
  simp

end Good

section TwoE

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem eltTwo_of_E_ff (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hF : HypF918 T V L V₁ Vp H K) (M : Subgroup G)
    (hHK : H = K ⊔ T) (hS : SQTKGroup ↥H) (hK0 : conjClosure K T ≠ K) (hTM : T ≤ M)
    (hker : kerIn (H ⊓ M) H = pCoreOf 2 H) {n : ℕ} (hn3 : 3 ≤ n) (hnodd : Odd n)
    (hKs : IsPSL 2 2 n ↥(E2.star (H ⊓ M) H K) ∨ IsSz n ↥(E2.star (H ⊓ M) H K))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    {I : Subgroup G} (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hWK : tildeOf V₁ ⁅conjClosure I H, conjClosure K T⁆ = tildeOf V₁ (conjClosure I H))
    (hne : ¬ tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆)
    (hE : IsFFInt (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
      (tildeOf (conjClosure I H) (conjClosure Vp H)) (hF.isElemAbelian_quotient (conjClosure I H))) :
    FFnatEltConcl hF M I := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFU := factElem hF (le_conjClosure Vp H)
  have hFE : Fact (IsElemAbelian 2 (tildeOf (conjClosure I H) (conjClosure Vp H))) :=
    ⟨hF.isElemAbelian_quotient (conjClosure I H)⟩
  have hWN : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hUN : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure Vp H
  have hV₁W : V₁ ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hWU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 hWU
  have hUV : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hV₁H : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hK₀H : conjClosure K T ≤ H := hF.K₀_le_H
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hK0
    refine le_antisymm (conjClosure_le fun t ht z hz => ?_) (le_conjClosure K T)
    exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
  obtain ⟨hKt, hK₀eq, hcomm, hperm⟩ := (five_group_data hF hS hA37 hA38 hK0).2 t htT htK
  have htH : t ∈ H := hF.T_le_H htT
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  set φ := actH hWN hUN with hφ
  have hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    actE_eq_one_of_mem_pCoreOf hF hV₁W hWN hUW hx
  have hnt : ¬ (conjClosure K T).subgroupOf H ≤ φ.ker := by
    intro h
    refine not_forall_comm_of_ne hWU hWK hne ?_
    intro k hk u hu
    have h1 := h (Subgroup.mem_subgroupOf.mpr hk : (⟨k, hK₀H hk⟩ : ↥H) ∈
      (conjClosure K T).subgroupOf H)
    exact (actE_eq_one_iff hWN hUN hUW ⟨k, hK₀H hk⟩).mp h1 u hu
  have hXH : conjClosure K T ⊔ T ≤ H := hF.K₀T_le_H
  have h3 : (conjClosure K T ⊔ T).subgroupOf H = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    exact hHK ▸ sup_le_sup_right (le_conjClosure K T) T
  have hFF : IsFFModule φ.range := by
    have h1 : IsFFModule (autOn (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
        (tildeOf (conjClosure I H) (conjClosure Vp H))) := hE
    rw [autOn_tilde_eq_map_actH hWN hUN hXH, h3, ← MonoidHom.range_eq_map] at h1
    exact h1
  obtain ⟨hAct, S, hSb⟩ :=
    kActionTwo_data hA21 h56 hF (H ⊓ M) hS hHK htT hKt hK₀eq hcomm hperm hker hn3 hnodd hKs hB
      hWN hUN hQ hnt hFF
  obtain ⟨b, hbN, r, hr, hyr, hgood⟩ := exists_good_pair φ (K.subgroupOf H) ⟨t, htH⟩ hAct S
  obtain ⟨k, hkM, hkb⟩ := hSb b hbN
  have hkM' : (k : G) ∈ M := (Subgroup.mem_inf.mp hkM).2
  have htM : t ∈ M := hTM htT
  set k' : ↥H := Subgroup.inclusion hKH k with hk'
  set t' : ↥H := ⟨t, htH⟩ with ht'
  set x : ↥H := k' * (t' * k' * t'⁻¹) with hx
  have hφx : φ x = (b : MulAut ↥(tildeOf (conjClosure I H) (conjClosure Vp H))) *
      (φ t' * (b : MulAut ↥(tildeOf (conjClosure I H) (conjClosure Vp H))) * (φ t')⁻¹) := by
    rw [hx, map_mul, map_mul, map_mul, map_inv]
    rw [hkb]
  obtain ⟨a, m', hm', hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hco : Nat.Coprime (2 ^ a) r := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hr)
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hco 0 1
  have hdvd : orderOf x ∣ e * m' := by
    have h2a : 2 ^ a ∣ e := (Nat.modEq_zero_iff_dvd).mp he0
    obtain ⟨c, hc'⟩ := h2a
    rw [hom, hc']
    exact ⟨c, by ring⟩
  have hxem : (x ^ e) ^ m' = 1 := by
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hφxe : φ (x ^ e) = (b : MulAut ↥(tildeOf (conjClosure I H) (conjClosure Vp H))) *
      (φ t' * (b : MulAut ↥(tildeOf (conjClosure I H) (conjClosure Vp H))) * (φ t')⁻¹) := by
    rw [map_pow, hφx, pow_eq_pow_mod e hyr, he1, ← pow_eq_pow_mod 1 hyr, pow_one]
  have hK₀U : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure Vp H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hK₀H.trans hUN)
  have hLeq : ((conjClosure K T).subgroupOf H).map φ = (K.subgroupOf H).map φ ⊔
      ((K.subgroupOf H).map (MulAut.conj t').toMonoidHom).map φ := by
    rw [← sup_map_conj_subgroupOf hKH htH hKtH hK₀eq, Subgroup.map_sup]
  have hlayer := layer_transfer (K₀ := conjClosure K T) hV₁W hWU hV₁H hWN hUN hUV hUW hK₀H hK₀U
    (x ^ e) (by
      rw [hLeq]
      intro e' he' hh
      rw [hφxe] at hh
      exact Subgroup.mem_inf.mpr ⟨hgood e' (Subgroup.mem_inf.mp hh).1, he'⟩)
  unfold FFnatEltConcl
  refine ⟨x ^ e, ?_, m', hm', ?_, hlayer⟩
  · rw [Subgroup.coe_pow]
    refine M.pow_mem ?_ e
    exact M.mul_mem hkM' (M.mul_mem (M.mul_mem htM hkM') (M.inv_mem htM))
  · intro a' _
    rw [← map_pow, hxem, map_one]
    rfl

end TwoE

end S153M

end CFSG.Quasithin
