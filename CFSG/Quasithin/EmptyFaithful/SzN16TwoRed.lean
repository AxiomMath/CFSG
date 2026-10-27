module

public import CFSG.Quasithin.EmptyFaithful.S153D16
public import CFSG.Quasithin.EmptyFaithful.S153DGen4
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.SzN16

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S153D
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_conjClosure {V L : Subgroup G} {g : G}
    (hL : g ∈ Subgroup.normalizer (L : Set G)) (hV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure V L : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), g ∈ Subgroup.normalizer (V : Set G) →
      ∀ x ∈ conjClosure V L, g * x * g⁻¹ ∈ conjClosure V L := by
    intro g hgL hgV x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      have e : g * (h * z * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure ((Subgroup.mem_normalizer_iff.1 hgL h).1 hh)
        ((Subgroup.mem_normalizer_iff.1 hgV z).1 hz)
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure V L).mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using (conjClosure V L).inv_mem ih
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hL hV x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hL) (inv_mem hV) _ hx
  simpa [mul_assoc] using this

theorem mem_centralizer_conjClosure {V L : Subgroup G} {t : G}
    (htV : t ∈ Subgroup.centralizer (V : Set G))
    (hO : ∀ l ∈ L, ⁅t, l⁆ ∈ Subgroup.centralizer (conjClosure V L : Set G)) :
    t ∈ Subgroup.centralizer (conjClosure V L : Set G) := by
  have hle : conjClosure V L ≤ Subgroup.centralizer ({t} : Set G) := by
    refine conjClosure_le fun h hh v hv => ?_
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hw : h * v * h⁻¹ ∈ conjClosure V L := mem_conjClosure hh hv
    have hc : (h * v * h⁻¹) * ⁅s, h⁆ = ⁅s, h⁆ * (h * v * h⁻¹) :=
      Subgroup.mem_centralizer_iff.1 (hO h hh) _ hw
    have hv' : s * v * s⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.1 htV v hv
      calc s * v * s⁻¹ = (s * v) * s⁻¹ := rfl
        _ = v := by rw [← this]; group
    have e1 : s * (h * v * h⁻¹) * s⁻¹ = (⁅s, h⁆ * h) * (s * v * s⁻¹) * (⁅s, h⁆ * h)⁻¹ := by
      simp only [commutatorElement_def]; group
    have e2 : s * (h * v * h⁻¹) * s⁻¹ = h * v * h⁻¹ := by
      rw [e1, hv']
      calc (⁅s, h⁆ * h) * v * (⁅s, h⁆ * h)⁻¹ = ⁅s, h⁆ * (h * v * h⁻¹) * ⁅s, h⁆⁻¹ := by group
        _ = (h * v * h⁻¹) * ⁅s, h⁆ * ⁅s, h⁆⁻¹ := by rw [← hc]
        _ = h * v * h⁻¹ := by group
    have : s * (h * v * h⁻¹) = (h * v * h⁻¹) * s := by
      have h3 := e2
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
    exact this
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  exact (Subgroup.mem_centralizer_iff.1 (hle hw) t rfl).symm

theorem mem_of_pow_mem_of_coprime {C : Subgroup G} {x : G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (h1 : x ^ m ∈ C) (h2 : x ^ n ∈ C) : x ∈ C := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have hx : x = (x ^ m) ^ a * (x ^ n) ^ b := by
    calc x = x ^ (a * m + b * n) := by rw [hab, zpow_one]
      _ = (x ^ m) ^ a * (x ^ n) ^ b := by
        rw [zpow_add, mul_comm a, zpow_mul, mul_comm b, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hx]
  exact C.mul_mem (C.zpow_mem h1 a) (C.zpow_mem h2 b)

theorem pow_three_mem_pCoreOf [Finite G] {T M V₁ Yp I : Subgroup G}
    (hF : Facts15311 T M V₁ Yp I) {y : G} (hy : y ∈ Yp) : y ^ 3 ∈ pCoreOf 2 Yp := by
  have h3 : ∀ x : OTwoQuot Yp, x ^ 3 = 1 := by
    rcases hF.struct_Yp with he | ⟨-, -, hexp⟩
    · obtain ⟨e⟩ := he
      intro x
      have h1 : e (x ^ 3) = 1 := by
        rw [map_pow]
        generalize e x = f
        have : ∀ z : ZMod 3, (3 : ℕ) • z = 0 := by decide
        ext i
        simp [this]
      exact e.injective (by simpa using h1)
    · exact hexp
  have := h3 (QuotientGroup.mk ⟨y, hy⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
  exact ⟨_, this, rfl⟩

section Odd

variable [Finite G]

theorem odd_card_center_quot (L : Subgroup G) :
    Odd (Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) := by
  by_contra h
  have h2 : 2 ∣ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : (z : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ 1 = 1 := by
    have h3 : z ^ 2 = 1 := by
      have h4 := pow_orderOf_eq_one z
      rwa [hz] at h4
    simpa using congrArg Subtype.val h3
  have hz1 : (z : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := eq_one_of_central_two_power z.2 hz2
  have hz1' : z = 1 := Subtype.ext hz1
  rw [hz1', orderOf_one] at hz
  omega

theorem mem_centralizer_of_central_two_power {L W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) {x : G} (hxL : x ∈ L)
    (hxc : ∀ l ∈ L, ⁅x, l⁆ ∈ pCoreOf 2 L) {k : ℕ}
    (hk : x ^ 2 ^ k ∈ Subgroup.centralizer (W : Set G)) :
    x ∈ Subgroup.centralizer (W : Set G) := by
  set ρ := autOnQuot hLW hker with hρ
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  set xt : ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk x' with hxt
  have hcent : xt ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    have hmem : (x' * l * x'⁻¹ * l⁻¹) ∈ CFSG.pCore 2 ↥L := by
      rw [mem_pCore_iff]
      have := hxc l l.2
      simpa [commutatorElement_def] using this
    have h1 : (QuotientGroup.mk (x' * l * x'⁻¹ * l⁻¹) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    have h2 : ⁅xt, (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L)⁆ = 1 := by
      rw [commutatorElement_def]
      simpa [hxt] using h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
  have hρk : ρ (xt ^ 2 ^ k) = 1 := by
    have : xt ^ 2 ^ k = QuotientGroup.mk (x' ^ 2 ^ k) := by rw [hxt, QuotientGroup.mk_pow]
    rw [this, hρ, autOnQuot_mk, autOnHom_eq_one_iff]
    simpa [hx'] using hk
  set Z := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) with hZ
  have hodd : Odd (Nat.card Z) := odd_card_center_quot L
  set n := Nat.card Z with hn
  have hxn : xt ^ n = 1 := by
    have h : (⟨xt, hcent⟩ : ↥Z) ^ n = 1 := pow_card_eq_one'
    have h2 := Subtype.ext_iff.1 h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hρx : ρ xt = 1 := by
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn1
      have hs2 : 2 ^ k * s = n * (2 ^ k * s / n) + 1 := by
        have := Nat.div_add_mod (2 ^ k * s) n
        omega
      have h5 : (xt ^ 2 ^ k) ^ s = xt := by
        rw [← pow_mul, hs2, pow_add, pow_mul, hxn, one_pow, one_mul, pow_one]
      calc ρ xt = ρ ((xt ^ 2 ^ k) ^ s) := by rw [h5]
        _ = 1 := by rw [map_pow, hρk, one_pow]
    · have hn0 : 0 < n := Nat.card_pos
      have hn1' : n = 1 := by omega
      have : xt = 1 := by simpa [hn1'] using hxn
      rw [this, map_one]
  have : autOnHom hLW x' = 1 := hρx
  exact (autOnHom_eq_one_iff hLW x').1 this

end Odd

section Main

variable [Finite G]

theorem isTwoReducedIn_conjClosure_sup {L R V : Subgroup G} (hRp : IsPGroup 2 ↥R)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hO : pCoreOf 2 (L ⊔ R) ≤ R)
    (hVR : R ≤ Subgroup.centralizer (V : Set G)) (hVe : IsElemAbelian 2 V)
    (hW : conjClosure V L ≤ centerOf (pCoreOf 2 (L ⊔ R)))
    (hqa : CFSG.IsQuasisimple ↥(autOn L (conjClosure V L))) :
    IsTwoReducedIn (L ⊔ R) (conjClosure V L) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := conjClosure V L with hWdef
  set H : Subgroup G := L ⊔ R with hH
  set O : Subgroup G := pCoreOf 2 L with hOdef
  set C : Subgroup G := Subgroup.centralizer (W : Set G) with hC
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRL
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure V L
  have hRW : R ≤ Subgroup.normalizer (W : Set G) := fun r hr =>
    mem_normalizer_conjClosure (hRL hr)
      (Subgroup.centralizer_le_normalizer _ (hVR hr))
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := sup_le hLW hRW
  have hWH : W ≤ H := fun w hw => pCoreOf_le 2 H (hW hw).1
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => (hW hb).2 a (hW ha).1
  have hWe : IsElemAbelian 2 W := by
    refine B2F.isElemAbelian_closure (S := {x | ∃ h ∈ L, ∃ z ∈ V, h * z * h⁻¹ = x}) ?_ ?_
    · intro a ha b hb
      exact hWc a (Subgroup.subset_closure ha) b (Subgroup.subset_closure hb)
    · rintro _ ⟨h, -, z, hz, rfl⟩
      rw [conj_pow, hVe.2 z hz, mul_one, mul_inv_cancel]
  refine ⟨hWH, hHW, hWe, ?_⟩
  intro D hDH hDN hD
  have hDL : D ≤ Subgroup.normalizer (L : Set G) := hDH.trans hHL
  have hDO : D ≤ Subgroup.normalizer (O : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hDL hg)
  have hOH : O ≤ pCoreOf 2 H := pCoreOf_le_pCoreOf_sup hRL
  have hOC : O ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun w hw => ((hW hw).2 x (hOH hx)).symm
  have hneq : ⁅L, D⁆ ≠ L := by
    intro heq
    have hLD : L ≤ D := by
      rw [← heq, Subgroup.commutator_le]
      intro l hl d hd
      have h1 : l * d * l⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.1 (hDN (Subgroup.mem_sup_left hl)) d).1 hd
      rw [commutatorElement_def]
      exact D.mul_mem h1 (D.inv_mem hd)
    have hpg : IsPGroup 2 ↥(autOn L W) := by
      rintro ⟨x, hx⟩
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hx
      obtain ⟨k, hk⟩ := hD (g : G) (hLD hg)
      refine ⟨k, Subtype.ext ?_⟩
      show (conjAct W g) ^ 2 ^ k = 1
      rw [← map_pow]
      exact InternalSec.conjAct_eq_one_of_mem_centralizer (g ^ 2 ^ k) (by simpa using hk)
    have hsolv : Group.IsSolvable ↥(autOn L W) := by
      have : Group.IsNilpotent ↥(autOn L W) := hpg.isNilpotent
      infer_instance
    exact not_isSolvable_of_isQuasisimple hqa hsolv
  have hA : ∀ j ∈ D, ∀ l ∈ L, ⁅j, l⁆ ∈ O :=
    forall_commutator_mem_of_comm_ne hperf hq hDL hDO hneq
  have hDLC : L ⊓ D ≤ C := fun x hx => by
    obtain ⟨k, hk⟩ := hD x hx.2
    exact mem_centralizer_of_central_two_power hLW hOC hx.1 (fun l hl => hA x hx.2 l hl) hk
  obtain ⟨T, hT, -⟩ := EscapingLocal.exists_isSylowTwoOf_ge (P := ⊥) (H := D) bot_le
    (hRp.to_le bot_le)
  have hOD_T : O ⊓ D ≤ T := by
    have h1 : O ⊓ D ≤ pCoreOf 2 D :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hDO hg, Subgroup.le_normalizer hg⟩)
        ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
    exact h1.trans (pCoreOf_le_of_isSylowTwoOf hT)
  have hZT : L ⊓ D ≤ Subgroup.normalizer (T : Set G) := by
    have key : ∀ z ∈ L ⊓ D, ∀ t ∈ T, z * t * z⁻¹ ∈ T := by
      intro z hz t ht
      have htD : t ∈ D := hT.1 ht
      have hc : ⁅t, z⁆ ∈ O := hA t htD z hz.1
      have hcD : ⁅t, z⁆ ∈ D := by
        rw [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem htD hz.2) (D.inv_mem htD)) (D.inv_mem hz.2)
      have hc' : ⁅z, t⁆ ∈ O ⊓ D := by
        rw [← commutatorElement_inv t z]
        exact ⟨O.inv_mem hc, D.inv_mem hcD⟩
      have e : z * t * z⁻¹ = ⁅z, t⁆ * t := by simp only [commutatorElement_def]; group
      rw [e]
      exact T.mul_mem (hOD_T hc') ht
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro t
    exact ⟨fun ht => key z hz t ht, fun ht => by
      have := key z⁻¹ (inv_mem hz) _ ht
      simpa [mul_assoc] using this⟩
  have hsplit : D ≤ (L ⊓ D) ⊔ (T ⊓ D) :=
    le_sup_inf_of_two_power hT le_rfl (hT.1.trans Subgroup.le_normalizer) hDL
      (fun d hd => InternalSec.two_of_sup hRp hRL d (hDH hd))
  have hDNT : D ≤ Subgroup.normalizer (T : Set G) :=
    hsplit.trans (sup_le hZT (inf_le_left.trans Subgroup.le_normalizer))
  have hTP : T ≤ pCoreOf 2 D := le_pCoreOf_of_le_normalizer 2 hT.1 hDNT hT.2.1
  have hPD : pCoreOf 2 D ≤ R :=
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 D).trans hDH)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 D (hDN hg)) (pCoreOf_isPGroup 2 D)).trans hO
  have hTC : T ≤ C := fun t ht =>
    mem_centralizer_conjClosure (hVR (hPD (hTP ht)))
      (fun l hl => hOC (hA t (hT.1 ht) l hl))
  exact hsplit.trans (sup_le (fun x hx => hDLC hx) (inf_le_left.trans hTC))

end Main

end CFSG.Quasithin.SzN16
