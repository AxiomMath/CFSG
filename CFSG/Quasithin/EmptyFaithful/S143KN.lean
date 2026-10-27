module

public import CFSG.Quasithin.EmptyFaithful.S143KM

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

theorem psi_add (c : Mat4) (v w : V4) : psi c (v.add w) = psi c v * psi c w := by
  unfold psi
  rw [vm_add, ofCoords_add]

section Block

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)
  {y : G} {cm : Mat4} (hM : KModel hS cm y)

include hS htT htRQ hM

theorem Setup.isA6Block : IsA6Block (kOf T M (c.Ac hrW hrV hr2)) (c.Ac hrW hrV hr2) := by
  have hB := hS.basis
  have hKN : kOf T M (c.Ac hrW hrV hr2) ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    c.kOf_le_normalizer_Ac hrW hrV hr2
  have hK := hM.K_le
  have hRUK := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hAK : c.Ac hrW hrV hr2 ≤ kOf T M (c.Ac hrW hrV hr2) :=
    (c.Ac_le_rOf hrW hrV hr2).trans (le_sup_left.trans hRUK)
  have hΓ2 := c.isPGroup_centralizer_Ac hrW hrV hr2
  have hsurj := homK_surjective hB hM.inj hK hM.x_K hM.y_K hM.count
  have hCle := hS.kOf_inf_centralizer_le htT htRQ hM
  set K := kOf T M (c.Ac hrW hrV hr2) with hKdef
  set A := c.Ac hrW hrV hr2 with hAdef
  set q := homK hB hM.inj hK with hq
  have hker : q.ker = A.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, homK_eq_one_iff, hB.cmat_eq_one_iff_mem_centralizer (hKN k.2),
      Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact hCle ⟨k.2, h⟩
    · intro h; exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => hB.comm a' ha' k h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 ↥A :=
    c.hyp.sylow.1.to_le ((c.Ac_le_rOf hrW hrV hr2).trans (rOf_le_T_of_hyp c.h1281))
  have hApc : A ≤ pCoreOf 2 K := le_pCoreOf_of_le_normalizer 2 hAK hKN hA2
  have hpc : CFSG.Open.pCore 2 ↥K = q.ker := by
    apply le_antisymm
    ·
      have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by norm_num)
      have hnormO : (CFSG.Open.pCore 2 ↥K).Normal := inferInstance
      have hnorm : ((CFSG.Open.pCore 2 ↥K).map q).Normal := hnormO.map q hsurj
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCore 2 ↥K).map q) with h | h
      · intro k hk
        have : q k ∈ (CFSG.Open.pCore 2 ↥K).map q := ⟨k, hk, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this
      · exfalso
        have hp2 : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥K).map q) := by
          rintro ⟨x, k, hk, rfl⟩
          obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 K ⟨(k : G), (mem_pCore_iff k).mp hk⟩
          refine ⟨m, Subtype.ext ?_⟩
          have h1 : (k : G) ^ 2 ^ m = 1 := congrArg Subtype.val hm
          have h2 : k ^ 2 ^ m = 1 := Subtype.ext h1
          show (q k) ^ 2 ^ m = 1
          rw [← map_pow, h2, map_one]
        rw [h] at hp2
        obtain ⟨n, hn⟩ := hp2.exists_card_eq
        have h360 : Nat.card ↥(⊤ : Subgroup ↥(alternatingGroup (Fin 6))) = 360 := by
          rw [Subgroup.card_top, card_alt6]
        rw [h360] at hn
        have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
    · rw [hker]
      intro k hk
      exact (mem_pCore_iff k).mpr (hApc hk)
  have hpCoreOf : A = pCoreOf 2 K := by
    show A = (CFSG.Open.pCore 2 ↥K).map K.subtype
    rw [hpc, hker, Subgroup.map_subgroupOf_eq_of_le hAK]
  refine ⟨oTwoUpper_kOf _, hpCoreOf, ?_⟩
  have hnormq : q.ker.Normal := q.normal_ker
  let φ : OTwoQuot K ≃* ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hsurj)
  let ψ₀ : ↥A →* N6 :=
    MonoidHom.mk' (fun a' => psi cm (coordsOf z a r r1 (a' : G))) (fun a₁ a₂ => by
      show psi cm (coordsOf z a r r1 ((a₁ : G) * (a₂ : G))) = _
      rw [hB.coordsOf_mul a₁.2 a₂.2, psi_add])
  have hψ₀inj : Function.Injective ψ₀ := fun a₁ a₂ h =>
    Subtype.ext (hB.coordsOf_inj a₁.2 a₂.2 (psi_inj hM.inj h))
  have hbij : Function.Bijective ψ₀ :=
    hψ₀inj.bijective_of_nat_card_le (by rw [n6_card, c.card_Ac hrW hrV hr2])
  let ψ : ↥A ≃* N6 := MulEquiv.ofBijective ψ₀ hbij
  have hφ : ∀ k : ↥K, ((φ (QuotientGroup.mk k) : ↥(alternatingGroup (Fin 6))) :
      Equiv.Perm (Fin 6)) = sigmaOfK hB hK k := fun k => by
    rw [show φ (QuotientGroup.mk k) = q k from rfl]
    exact homK_apply hB hM.inj hK k
  refine ⟨φ, ψ, fun k a' h => ?_⟩
  rw [hφ k]
  show psi cm (coordsOf z a r r1 ((k : G) * (a' : G) * (k : G)⁻¹)) =
    n6Act (sigmaOfK hB hK k) (psi cm (coordsOf z a r r1 (a' : G)))
  rw [hB.cmat_spec (hKN k.2) a'.2, (sigmaOfK_spec hB hK k).2]

end Block

end S143

end CFSG.Quasithin
