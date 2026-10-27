module

public import CFSG.Quasithin.EmptyFaithful.SBc9Gen
public import CFSG.Quasithin.EmptyFaithful.ModDGlue
public import CFSG.Quasithin.EmptyFaithful.SBc10G2Mod
public import CFSG.Quasithin.EmptyFaithful.SBc8V2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.CosetTable CFSG.Quasithin.ModD
open scoped commutatorElement IsMulCommutative

namespace SBc10

section Main

variable
  {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem g2_facts (h113 : StageLemma14113) (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) (hG2 : IsG2Block L) :
    (∀ q ∈ blockU L, q ∈ Subgroup.centralizer (Yp : Set G) → q ∈ blockZ L) ∧
      ∀ q ∈ blockU L, ∃ r ∈ ⁅blockU L, Yp⁆, r⁻¹ * q ∈ blockZ L := by
  classical
  have hshort : IsShort2 L := hG2.1
  obtain ⟨-, hV₂Q, hMN, hV₂card, hV₂fix⟩ := SBc8.V₂_facts h113 c
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hSM : Sgp153 T V₁ ≤ M ⊓ I := le_inf (inf_le_right.trans c.c29.norm_le) hsyl.1
  have hYM : Yp ≤ M ⊓ I := by
    rw [hF.yp_eq]
    exact SBc5.oPrimeResidualOf_le 3 _
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := SBc7.Sgp_le_normalizer_Yp c
  have hLQ : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 L) L
  let P : Sylow 2 ↥L := B6.toSylow2 hQsyl
  have hPcoe : (P : Subgroup ↥L) = (Sgp153 T V₁ ⊓ L).subgroupOf L := B6.toSylow2_coe hQsyl
  obtain ⟨ψ, hψs, hψk, hψP⟩ := exists_psi hG2.2.1 P
  obtain ⟨φ, hφ⟩ := exists_phi hshort ψ hψs hψk
  obtain ⟨hQP, hQc, hQ2⟩ := SBc9.blockU_facts hshort
  have hcomm : IsMulCommutative ↥(blockU L) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (hQc a a.2 b b.2)
  have hsq : ∀ a : ↥(blockU L), a * a = 1 := fun a => Subtype.ext (hQ2 a a.2)
  have hZU : blockZ L ≤ blockU L := inf_le_left
  let Z' : Subgroup ↥(blockU L) := (blockZ L).subgroupOf (blockU L)
  have hcardU : Nat.card (↥(blockU L) ⧸ Z') = 2 ^ 6 := hG2.2.2.1
  have hZfix : ∀ g : U33G, ∀ ζ ∈ Z', φ g ζ = ζ := by
    intro g ζ hζ
    obtain ⟨k, rfl⟩ := hψs g
    apply Subtype.ext
    rw [hφ]
    have hζc : (ζ : G) ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_subgroupOf.1 hζ).2
    have h1 := Subgroup.mem_centralizer_iff.1 hζc (k : G) k.2
    show (k : G) * (ζ : G) * (k : G)⁻¹ = (ζ : G)
    rw [h1, mul_inv_cancel_right]
  have hirr : ∀ N : Subgroup ↥(blockU L), Z' ≤ N → (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) →
      N = Z' ∨ N = ⊤ := by
    intro N hZN hN
    have hfwd : ∀ k ∈ L, ∀ h ∈ N.map (blockU L).subtype, k * h * k⁻¹ ∈ N.map (blockU L).subtype := by
      intro k hk h hh
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
      refine Subgroup.mem_map.2 ⟨φ (ψ ⟨k, hk⟩) n, hN _ n hn, ?_⟩
      exact hφ ⟨k, hk⟩ n
    have hnorm : L ≤ Subgroup.normalizer ((N.map (blockU L).subtype : Subgroup G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hfwd k hk h, fun hh => ?_⟩
      have h1 := hfwd k⁻¹ (L.inv_mem hk) _ hh
      have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
      rwa [e] at h1
    have hZW : blockZ L ≤ N.map (blockU L).subtype := by
      intro x hx
      exact Subgroup.mem_map.2 ⟨⟨x, hZU hx⟩, hZN (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    rcases hshort.2.2.2.2.2 (N.map (blockU L).subtype) hZW
      (Subgroup.map_subtype_le N) hnorm with h | h
    · left
      apply Subgroup.map_injective (blockU L).subtype_injective
      rw [h]
      exact (Subgroup.map_subgroupOf_eq_of_le hZU).symm
    · right
      apply Subgroup.map_injective (blockU L).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  let φ' : U33G →* MulAut (↥(blockU L) ⧸ Z') := actQ φ Z' hZfix
  have hφ' : ∀ g x, φ' g (QuotientGroup.mk x) = QuotientGroup.mk (φ g x) :=
    fun g x => actQ_mk φ Z' hZfix g x
  have hsq' : ∀ a : ↥(blockU L) ⧸ Z', a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, hsq x]
      rfl
  have hirr' : ∀ N : Subgroup (↥(blockU L) ⧸ Z'), (∀ g : U33G, ∀ n ∈ N, φ' g n ∈ N) →
      N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let N' : Subgroup ↥(blockU L) := N.comap (QuotientGroup.mk' Z')
    have hZN : Z' ≤ N' := by
      intro x hx
      show (QuotientGroup.mk x : ↥(blockU L) ⧸ Z') ∈ N
      rw [(QuotientGroup.eq_one_iff x).2 hx]
      exact N.one_mem
    have hinv : ∀ g : U33G, ∀ n ∈ N', φ g n ∈ N' := by
      intro g n hn
      show (QuotientGroup.mk (φ g n) : ↥(blockU L) ⧸ Z') ∈ N
      rw [← hφ']
      exact hN g _ hn
    rcases hirr N' hZN hinv with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ N' := hx
      rw [h] at hu
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff u).2 hu)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ N' := by rw [h]; trivial
      exact hu
  let Ybar : Subgroup U33G := (Yp.subgroupOf L).map ψ
  have hTY : ∀ τ ∈ u33Data.T, ∀ y ∈ Ybar, τ * y * τ⁻¹ ∈ Ybar := by
    intro τ hτ y hy
    rw [← hψP] at hτ
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hτ
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    refine ⟨p * y₀ * p⁻¹, ?_, by simp⟩
    rw [hPcoe] at hp
    have hpS : (p : G) ∈ Sgp153 T V₁ := (Subgroup.mem_subgroupOf.mp hp).1
    show (p : G) * (y₀ : G) * (p : G)⁻¹ ∈ Yp
    exact (Subgroup.mem_normalizer_iff.mp (hSN hpS) (y₀ : G)).mp hy₀
  let V₂' : Subgroup ↥(blockU L) := V₂.subgroupOf (blockU L)
  have hZV : ∀ w : G, w ∈ V₂ → w ∈ blockZ L → w = 1 := by
    intro w hwV hwZ
    by_contra hw1
    obtain ⟨y, hy, hne⟩ := hV₂fix w hwV hw1
    apply hne
    have h := Subgroup.mem_centralizer_iff.mp hwZ.2 y (hYL hy)
    calc y * w * y⁻¹ = (w * y) * y⁻¹ := by rw [h]
      _ = w := by group
  have hVZ : V₂' ⊓ Z' = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwV, hwZ⟩
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hZV (w : G) hwV hwZ)
  have hinjV : ∀ a ∈ V₂', ∀ b ∈ V₂', (QuotientGroup.mk a : ↥(blockU L) ⧸ Z') = QuotientGroup.mk b →
      a = b := by
    intro a ha b hb h
    have h1 : a⁻¹ * b ∈ Z' := QuotientGroup.eq.1 h
    have h2 : a⁻¹ * b ∈ V₂' := V₂'.mul_mem (V₂'.inv_mem ha) hb
    have h3 : a⁻¹ * b ∈ V₂' ⊓ Z' := ⟨h2, h1⟩
    rw [hVZ] at h3
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 h3)
  let E : Subgroup (↥(blockU L) ⧸ Z') := V₂'.map (QuotientGroup.mk' Z')
  have hE4 : Nat.card ↥E = 4 := by
    have hV₂' : Nat.card ↥V₂' = 4 := by
      have h1 : Nat.card ↥V₂' = Nat.card ↥V₂ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂Q).toEquiv
      rw [h1]
      exact hV₂card
    have h1 : Nat.card ↥E = Nat.card ↥V₂' := by
      symm
      refine Nat.card_congr (Equiv.ofBijective
        (fun v : V₂' => (⟨QuotientGroup.mk' Z' v, v, v.2, rfl⟩ : ↥E)) ⟨?_, ?_⟩)
      · intro a b h
        have h' : (QuotientGroup.mk (a : ↥(blockU L)) : ↥(blockU L) ⧸ Z') =
            QuotientGroup.mk (b : ↥(blockU L)) := congrArg Subtype.val h
        exact Subtype.ext (hinjV a a.2 b b.2 h')
      · rintro ⟨x, v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [h1]
    exact hV₂'
  have hET : ∀ τ ∈ u33Data.T, ∀ e ∈ E, φ' τ e ∈ E := by
    intro τ hτ e he
    rw [← hψP] at hτ
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hτ
    obtain ⟨v, hv, rfl⟩ := he
    rw [hPcoe] at hp
    have hpS : (p : G) ∈ Sgp153 T V₁ := (Subgroup.mem_subgroupOf.mp hp).1
    have hpv : (p : G) * (v : G) * (p : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hMN (hSM hpS)) (v : G)).mp hv
    refine ⟨φ (ψ p) v, ?_, ?_⟩
    · show ((φ (ψ p) v : ↥(blockU L)) : G) ∈ V₂
      rw [hφ]
      exact hpv
    · show (QuotientGroup.mk (φ (ψ p) v) : ↥(blockU L) ⧸ Z') = φ' (ψ p) (QuotientGroup.mk v)
      rw [hφ']
  have hEY : ∀ y ∈ Ybar, ∀ e ∈ E, φ' y e ∈ E := by
    intro y hy e he
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨v, hv, rfl⟩ := he
    have hy₀Yp : (y₀ : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hy₀
    have hyv : (y₀ : G) * (v : G) * (y₀ : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hMN (hYM hy₀Yp)) (v : G)).mp hv
    refine ⟨φ (ψ y₀) v, ?_, ?_⟩
    · show ((φ (ψ y₀) v : ↥(blockU L)) : G) ∈ V₂
      rw [hφ]
      exact hyv
    · show (QuotientGroup.mk (φ (ψ y₀) v) : ↥(blockU L) ⧸ Z') = φ' (ψ y₀) (QuotientGroup.mk v)
      rw [hφ']
  have hCE : ∀ e ∈ E, (∀ y ∈ Ybar, φ' y e = e) → e = 1 := by
    rintro _ ⟨v, hv, rfl⟩ hfix
    by_contra hne
    have hv1 : (v : G) ≠ 1 := by
      intro h
      apply hne
      have : v = 1 := Subtype.ext h
      rw [this]
      exact map_one _
    obtain ⟨y, hy, hyne⟩ := hV₂fix (v : G) hv hv1
    have hyL : y ∈ L := hYL hy
    have hyv : y * (v : G) * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hMN (hYM hy)) (v : G)).mp hv
    have h1 := hfix (ψ ⟨y, hyL⟩) ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have h2 : (QuotientGroup.mk (φ (ψ ⟨y, hyL⟩) v) : ↥(blockU L) ⧸ Z') = QuotientGroup.mk' Z' v := by
      rw [← hφ']
      exact h1
    have h3 : (φ (ψ ⟨y, hyL⟩) v)⁻¹ * v ∈ Z' := QuotientGroup.eq.1 h2
    have h4 : (((φ (ψ ⟨y, hyL⟩) v)⁻¹ * v : ↥(blockU L)) : G) ∈ blockZ L :=
      Subgroup.mem_subgroupOf.mp h3
    have h5 : (((φ (ψ ⟨y, hyL⟩) v)⁻¹ * v : ↥(blockU L)) : G) = (y * (v : G) * y⁻¹)⁻¹ * (v : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ ⟨y, hyL⟩ v]
    rw [h5] at h4
    have h6 : (y * (v : G) * y⁻¹)⁻¹ * (v : G) = 1 :=
      hZV _ (V₂.mul_mem (V₂.inv_mem hyv) hv) h4
    exact hyne (inv_mul_eq_one.1 h6)
  obtain ⟨hfixM, hH⟩ := g2_module_facts (M := ↥(blockU L) ⧸ Z') hcardU hsq' φ' hirr' hTY hE4 hET hEY hCE
  refine ⟨?_, ?_⟩
  · intro q hq hqC
    have h1 : (QuotientGroup.mk (⟨q, hq⟩ : ↥(blockU L)) : ↥(blockU L) ⧸ Z') = 1 := by
      apply hfixM
      rintro _ ⟨y, hy, rfl⟩
      rw [hφ']
      have hyq : ((φ (ψ y) ⟨q, hq⟩ : ↥(blockU L)) : G) = q := by
        rw [hφ]
        have h := Subgroup.mem_centralizer_iff.mp hqC y (Subgroup.mem_subgroupOf.mp hy)
        calc (y : G) * q * (y : G)⁻¹ = (q * (y : G)) * (y : G)⁻¹ := by rw [h]
          _ = q := by group
      have : φ (ψ y) ⟨q, hq⟩ = ⟨q, hq⟩ := Subtype.ext hyq
      rw [this]
    have h2 : (⟨q, hq⟩ : ↥(blockU L)) ∈ Z' := (QuotientGroup.eq_one_iff _).1 h1
    exact Subgroup.mem_subgroupOf.mp h2
  · let R : Subgroup G := ⁅blockU L, Yp⁆
    let H : Subgroup (↥(blockU L) ⧸ Z') := (R.subgroupOf (blockU L)).map (QuotientGroup.mk' Z')
    have hHtop : H = ⊤ := by
      apply hH H
      rintro _ ⟨y, hy, rfl⟩ m
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective m
      have hy' : (y : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hy
      have hcomm' : (y : G) * (q : G) * (y : G)⁻¹ * (q : G)⁻¹ ∈ R := by
        have h := Subgroup.commutator_mem_commutator hy' q.2
        rw [Subgroup.commutator_comm, commutatorElement_def] at h
        exact h
      refine ⟨φ (ψ y) q * q⁻¹, ?_, ?_⟩
      · show (((φ (ψ y) q * q⁻¹ : ↥(blockU L))) : G) ∈ R
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ y q]
        exact hcomm'
      · show QuotientGroup.mk (φ (ψ y) q * q⁻¹) = φ' (ψ y) (QuotientGroup.mk q) * (QuotientGroup.mk q)⁻¹
        rw [hφ', QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    intro q hq
    have hmem : (QuotientGroup.mk (⟨q, hq⟩ : ↥(blockU L)) : ↥(blockU L) ⧸ Z') ∈ H := by
      rw [hHtop]
      trivial
    obtain ⟨r, hr, hrq⟩ := hmem
    refine ⟨(r : G), Subgroup.mem_subgroupOf.mp hr, ?_⟩
    have h1 : r⁻¹ * ⟨q, hq⟩ ∈ Z' := QuotientGroup.eq.1 hrq
    exact Subgroup.mem_subgroupOf.mp h1

end Main

end SBc10

end CFSG.Quasithin
