module

public import CFSG.Quasithin.H13.A6S1354
public import CFSG.Quasithin.H13.A6Producer4
public import Certificates.Certificate17016
import CFSG.GroupTheory.PCore.OpenTransport


public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem eq_one_of_comm_three : ∀ σ : Perm (Fin 6),
    σ * (swap 0 1 * swap 1 2) = swap 0 1 * swap 1 2 * σ →
    σ * (swap 3 4 * swap 4 5) = swap 3 4 * swap 4 5 * σ →
    σ * (swap 0 3 * swap 1 4) = swap 0 3 * swap 1 4 * σ → σ = 1 :=
  Certificates.certificate17016.1

theorem redWit : ∀ σ : Perm (Fin 6), σ ≠ 1 → RedWit σ :=
  Certificates.certificate17016.2.1

theorem redList_sign : ∀ τ ∈ RedList, Perm.sign τ = 1 :=
  Certificates.certificate17016.2.2.1

theorem pow_four_of_pow_sixteen : ∀ σ : Perm (Fin 6), σ ^ 16 = 1 → σ ^ 4 = 1 :=
  Certificates.certificate17016.2.2.2

theorem pow_four_of_pow_two_pow
    {σ : Perm (Fin 6)} {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 4 = 1 := by
  refine pow_four_of_pow_sixteen σ ?_
  have h1 := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf σ ∣ 720 := by
    have := orderOf_dvd_card (x := σ)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  rw [hjeq] at h2
  have hj4 : j ≤ 4 := by
    by_contra hj4
    have : 2 ^ 5 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
    have := this.trans h2
    norm_num at this
  rw [← orderOf_dvd_iff_pow_eq_one, hjeq]
  exact Nat.pow_dvd_pow 2 hj4 |>.trans (by norm_num)

theorem nat_card_alt_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

variable {G : Type} [Group G]

theorem mem_pCore_iff {L : Subgroup G} (x : ↥L) : x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L :=
  (CFSG.mem_openPCoreOf_iff x).symm

theorem comm_mem_of_mem_o2Z {L : Subgroup G} {c l : G} (hc : c ∈ o2Z L) (hl : l ∈ L) :
    c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨c', hc', rfl⟩ := hc
  have hz : ∀ q : ↥L ⧸ CFSG.pCore 2 ↥L, q * (c' : ↥L ⧸ CFSG.pCore 2 ↥L) =
      (c' : ↥L ⧸ CFSG.pCore 2 ↥L) * q := Subgroup.mem_center_iff.mp hc'
  have h1 : (c' * ⟨l, hl⟩ * c'⁻¹ * (⟨l, hl⟩ : ↥L)⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      ← hz ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)]
    group
  exact (mem_pCore_iff _).1 h1

namespace Setting4

variable [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem rho_eq_one_iff (g : ↥(Subgroup.normalizer (V : Set G))) :
    S.frame.ρ g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := (S.conj_eq_iff g ⟨v, hv⟩).2 (by rw [h, map_one, MulAut.one_apply])
    calc v * g = g * v * (g : G)⁻¹ * g := by rw [this]
      _ = g * v := by group
  · intro h
    apply act4_injective
    refine MulEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    have := (S.conj_eq_iff g v).1 (by
      have := Subgroup.mem_centralizer_iff.mp h v v.2
      calc (g : G) * v * (g : G)⁻¹ = v * g * (g : G)⁻¹ := by rw [this]
        _ = v := by group)
    rw [map_one, MulAut.one_apply]
    exact this

theorem elemAbelian_V : IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => S.frame.ψ.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩,
    fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : ↥V) ^ 2 = 1 := by
    apply S.frame.ψ.injective
    rw [map_pow, map_one, pow_two]
    exact Subtype.ext (sq_W4 _)
  simpa using congrArg Subtype.val h

theorem isTwoLocal_NV : IsTwoLocal (Subgroup.normalizer (V : Set G)) := by
  refine ⟨V, ?_, S.isPGroup_V, rfl⟩
  intro h
  have := S.card_V
  rw [h, Subgroup.card_bot] at this
  omega

theorem NV_le_M : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge S.isTwoLocal_NV
  have h := S.uniqueM.2 M' ⟨hM', (sup_le S.frame.L_le S.frame.T_le).trans hM'le⟩
  exact h ▸ hM'le

theorem reduced : IsTwoReducedIn (L ⊔ T) V := by
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  refine isTwoReducedIn_of_comm (S.V_le_T.trans le_sup_right) hLTV S.elemAbelian_V
    fun g hg hcomm => ?_
  refine (S.rho_eq_one_iff ⟨g, hLTV hg⟩).1 ?_
  by_contra hne
  obtain ⟨τ, hτR, hτ4⟩ := redWit _ hne
  obtain ⟨l, hlL, rfl⟩ :=
    (S.frame.image_L τ).2 (Perm.mem_alternatingGroup.2 (redList_sign τ hτR))
  obtain ⟨k, hk⟩ := hcomm l hlL
  apply hτ4
  have h1 : S.frame.ρ ((⟨g, hLTV hg⟩ * l * ⟨g, hLTV hg⟩⁻¹ * l⁻¹) ^ 2 ^ k) = 1 :=
    (S.rho_eq_one_iff _).2 (by simpa using hk)
  rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact pow_four_of_pow_two_pow h1

theorem pCoreOf_L_le_centralizer
    : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
  (pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_centralizer_of_reduced S.reduced)

theorem pCoreOf_L_le_T : pCoreOf 2 L ≤ T :=
  (pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)

theorem centralizer_le_o2Z
    : L ⊓ Subgroup.centralizer (V : Set G) ≤ o2Z L := by
  obtain ⟨e⟩ := S.centralQuot
  let π₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let π₂ := QuotientGroup.mk' (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  let φ : ↥L →* ↥(alternatingGroup (Fin 6)) := e.toMonoidHom.comp (π₂.comp π₁)
  have hφ : Function.Surjective φ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hkerφ : ∀ x : ↥L, φ x = 1 ↔ π₁ x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro x
    show e (π₂ (π₁ x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  let ρL : ↥L →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)
  have hρL : ∀ x : ↥L, ρL x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := fun x =>
    S.rho_eq_one_iff _
  have hlift : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → ∃ l : ↥L, ρL l = σ := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
    exact ⟨⟨g, hgL⟩, hg⟩
  have hrange : ρL.range = alternatingGroup (Fin 6) := by
    ext σ
    constructor
    · rintro ⟨l, rfl⟩
      exact (S.frame.image_L _).1 ⟨_, l.2, rfl⟩
    · intro hσ
      obtain ⟨l, hl⟩ := hlift σ hσ
      exact ⟨l, hl⟩
  have hle : φ.ker ≤ ρL.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    have hzc := Subgroup.mem_center_iff.mp ((hkerφ z).1 hz)
    have hcomm : ∀ l : ↥L, ρL z * ρL l = ρL l * ρL z := by
      intro l
      have h1 : π₁ (z * l * z⁻¹ * l⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hzc (π₁ l)]
        group
      have h2 : z * l * z⁻¹ * l⁻¹ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h1
      have h3 := (hρL _).2 (S.pCoreOf_L_le_centralizer ((mem_pCore_iff _).1 h2))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
      calc ρL z * ρL l = (ρL z * ρL l * (ρL z)⁻¹ * (ρL l)⁻¹) * (ρL l * ρL z) := by group
        _ = ρL l * ρL z := by rw [h3, one_mul]
    obtain ⟨l1, hl1⟩ := hlift (swap 0 1 * swap 1 2)
      (Perm.mem_alternatingGroup.2 (by decide))
    obtain ⟨l2, hl2⟩ := hlift (swap 3 4 * swap 4 5)
      (Perm.mem_alternatingGroup.2 (by decide))
    obtain ⟨l3, hl3⟩ := hlift (swap 0 3 * swap 1 4)
      (Perm.mem_alternatingGroup.2 (by decide))
    exact eq_one_of_comm_three _ (hl1 ▸ hcomm l1) (hl2 ▸ hcomm l2) (hl3 ▸ hcomm l3)
  have hcardφ : Nat.card ↥L = Nat.card φ.ker * 360 := by
    rw [← nat_card_alt_six,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hcardρ : Nat.card ↥L = Nat.card ρL.ker * 360 := by
    rw [← nat_card_alt_six, ← hrange,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρL).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρL.ker
  have heq : φ.ker = ρL.ker := Subgroup.eq_of_le_of_card_ge hle (by omega)
  intro x hx
  have hxk : (⟨x, hx.1⟩ : ↥L) ∈ ρL.ker := (hρL _).2 hx.2
  rw [← heq, MonoidHom.mem_ker, hkerφ] at hxk
  exact ⟨⟨x, hx.1⟩, hxk, rfl⟩

theorem comm_mem_pCoreOf {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) {l : G}
    (hl : l ∈ L) : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L :=
  comm_mem_of_centralizer (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) S.h13.faithful.1.2.1.2.1 S.frame.L_le
    (fun _ hc _ hl => comm_mem_of_mem_o2Z (S.centralizer_le_o2Z hc) hl) hy.1 hy.2 hl

theorem cT
    : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
  inf_centralizer_eq_pCoreOf S.h13.sylow.1 (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
    S.frame.L_le S.frame.T_le (pCoreOf_le_centralizer_of_reduced S.reduced)
    fun _ hl _ ht => S.pCoreOf_L_le_T (S.comm_mem_pCoreOf ⟨S.T_le_NL ht.1, ht.2⟩ hl)

end Setting4

end CFSG.Quasithin.H13.A6
