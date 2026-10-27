module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGCenterCoprime (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ¬ p ∣ Nat.card ψ.ker

@[expose] def GGNoInvariantLineTorus (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eh : Subgroup (MulAut R), (Eh : Set (MulAut R)) ⊆ I → IsElemAbelian p Eh →
    p ^ r ≤ Nat.card Eh → p ^ 3 ≤ Nat.card Eh →
    GGCenterCoprime p R ∧
    ∀ Λ : Subgroup (MulAut R), Λ ≤ Eh → Nat.card Λ = p →
      ∃ w : R, MulAut.conj w ∈ Subgroup.normalizer (Eh : Set (MulAut R)) ∧
        ∃ e ∈ Λ, MulAut.conj w * e * (MulAut.conj w)⁻¹ ∉ Λ

section Elementary

open scoped Pointwise

variable {G : Type} [Group G]

theorem pow_mem_of_mem_sup {p : ℕ} {L Bs : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hexp : ∀ b ∈ Bs, b ^ p = 1) {c : G}
    (hc : c ∈ L ⊔ Bs) : c ^ p ∈ L := by
  have hc' : c ∈ (L : Set G) * (Bs : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L Bs hBsN]
    exact hc
  obtain ⟨l, hl, b, hb, rfl⟩ := hc'
  have key : ∀ k : ℕ, (l * b) ^ k * (b ^ k)⁻¹ ∈ L := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hbk : b ^ k ∈ Subgroup.normalizer (L : Set G) := hBsN (pow_mem hb k)
      have h1 : b ^ k * l * (b ^ k)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hbk l).mp hl
      have h2 : (l * b) ^ (k + 1) * (b ^ (k + 1))⁻¹ =
          ((l * b) ^ k * (b ^ k)⁻¹) * (b ^ k * l * (b ^ k)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [h2]
      exact mul_mem ih h1
  have h := key p
  rwa [hexp b hb, inv_one, mul_one] at h

theorem ggLAut_of_mem {L : Subgroup G} {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (l : L) (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)) :
    ggLAut L θ ⟨l, hl⟩ = MulAut.conj (ggQuotHom θ l) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [ggLAut_apply, MulAut.conj_apply, ggQuotHom_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1

end Elementary

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_normalizer_lift {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    (w : R) (hw : MulAut.conj w ∈
      Subgroup.normalizer (((ggBeta L θ hBsN).range : Subgroup (MulAut R)) : Set (MulAut R))) :
    ∃ (n : G) (hn : n ∈ Subgroup.normalizer (L : Set G)), n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ e ∈ (ggBeta L θ hBsN).range,
        ggLAut L θ ⟨n, hn⟩ * e * (ggLAut L θ ⟨n, hn⟩)⁻¹ =
          MulAut.conj w * e * (MulAut.conj w)⁻¹ := by
  have := Fact.mk hp
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  set β := ggBeta L θ hBsN with hβ
  set NL := Subgroup.normalizer (L : Set G) with hNL
  have hEhA : IsElemAbelian p β.range := isElemAbelian_range_ggBeta θ hBs hBsN
  obtain ⟨l, hl⟩ := ggQuotHom_surjective θ w
  have hlN : (l : G) ∈ NL := Subgroup.le_normalizer l.2
  have hlA : ggLAut L θ ⟨l, hlN⟩ = MulAut.conj w := by rw [ggLAut_of_mem, hl]
  set V : Subgroup G := (β.range.comap (ggLAut L θ)).map NL.subtype ⊓ (L ⊔ Bs) with hV
  have hVN : V ≤ NL := by
    rintro _ ⟨⟨y, -, rfl⟩, -⟩
    exact y.2
  have hmemV : ∀ (g : G) (hg : g ∈ NL), g ∈ L ⊔ Bs → ggLAut L θ ⟨g, hg⟩ ∈ β.range → g ∈ V :=
    fun g hg h1 h2 => ⟨⟨⟨g, hg⟩, h2, rfl⟩, h1⟩
  have hVE : ∀ (g : G) (hg : g ∈ V), ggLAut L θ ⟨g, hVN hg⟩ ∈ β.range := by
    rintro _ ⟨⟨y, hy, rfl⟩, -⟩
    exact hy
  have hVLB : V ≤ L ⊔ Bs := inf_le_right
  have hBsV : Bs ≤ V := fun b hb =>
    hmemV b (hBsN hb) (Subgroup.mem_sup_right hb) ⟨⟨b, hb⟩, rfl⟩
  let κ : ↥V →* MulAut R := (ggLAut L θ).comp (Subgroup.inclusion hVN)
  have hκr : κ.range = β.range := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hVE v v.2
    · rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBsV b.2⟩, rfl⟩
  have hκk : ∀ v : ↥V, κ v = 1 → (v : G) ∈ Subgroup.centralizer (L : Set G) := fun v hv =>
    mem_centralizer_of_ggLAut_eq_one L θ hL hv
  have hexpk : ∀ c : ↥κ.ker, ∀ k : ℕ, c ^ p ^ k = 1 → c ^ p = 1 := by
    intro c k hck
    set g : G := ((c : ↥V) : G) with hg
    have hgC : g ∈ Subgroup.centralizer (L : Set G) := hκk c c.2
    have hgk : g ^ p ^ k = 1 := by
      have := congrArg (fun z : ↥κ.ker => ((z : ↥V) : G)) hck
      simpa [hg] using this
    have hgp : g ^ p ∈ L := pow_mem_of_mem_sup hBsN (fun b hb => hBs.2 b hb) (hVLB (c : ↥V).2)
    have hz : (⟨g ^ p, hgp⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (pow_mem hgC p) m m.2)
    set z : Subgroup.center L := ⟨⟨g ^ p, hgp⟩, hz⟩ with hzdef
    have hzk : z ^ p ^ k = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (g ^ p) ^ p ^ k = 1
      rw [← pow_mul, mul_comm, pow_mul, hgk, one_pow]
    have hcop : Nat.Coprime (p ^ k) (Nat.card (Subgroup.center L)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ)
    have hz1 : orderOf z = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzk) (orderOf_dvd_natCard z)
    rw [orderOf_eq_one_iff] at hz1
    have hgp1 : g ^ p = 1 := by
      have := congrArg (fun y : Subgroup.center L => ((y : L) : G)) hz1
      simpa [hzdef] using this
    apply Subtype.ext
    apply Subtype.ext
    simpa [hg] using hgp1
  have hk2 : ¬ p ^ 2 ∣ Nat.card κ.ker := by
    intro hdvd
    obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
    set K : Subgroup G := (K₂.map κ.ker.subtype).map V.subtype with hK
    have hKcard : Nat.card K = p ^ 2 := by
      rw [hK, Subgroup.card_map_of_injective V.subtype_injective,
        Subgroup.card_map_of_injective κ.ker.subtype_injective, hK₂]
    have hKC : K ≤ Subgroup.centralizer (L : Set G) := by
      rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
      exact hκk c c.2
    have hKcyc := hcyc K hKC (IsPGroup.of_card hKcard)
    have hKexp : ∀ y ∈ K, y ^ p = 1 := by
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      obtain ⟨k, hk⟩ := (IsPGroup.of_card hK₂) ⟨c, hc⟩
      have h1 : c ^ p ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have h2 := hexpk c k h1
      have := congrArg (fun z : ↥κ.ker => ((z : ↥V) : G)) h2
      simpa using this
    have h1 := card_le_of_isCyclic hp.pos hKcyc hKexp
    rw [hKcard] at h1
    nlinarith [hp.two_le]
  have hcV := card_range_mul_card_ker κ
  rw [hκr] at hcV
  have hcE := card_range_ggBeta_mul_of hp hBs hxBs hx1 hLx hcyc hL θ hBsN
  have hidx : Bs.relIndex V * Nat.card Bs = Nat.card V := by
    have h1 := Subgroup.relIndex_mul_card Bs V
    rwa [inf_eq_left.mpr hBsV] at h1
  have hrel : Bs.relIndex V * p = Nat.card κ.ker := by
    have hE0 : 0 < Nat.card β.range := Nat.card_pos
    have h1 : Bs.relIndex V * p * Nat.card β.range = Nat.card κ.ker * Nat.card β.range := by
      calc Bs.relIndex V * p * Nat.card β.range = Bs.relIndex V * (Nat.card β.range * p) := by
            ring
        _ = Nat.card V := by rw [hcE, hidx]
        _ = Nat.card β.range * Nat.card κ.ker := hcV.symm
        _ = Nat.card κ.ker * Nat.card β.range := by ring
    exact Nat.eq_of_mul_eq_mul_right hE0 h1
  have hpidx : ¬ p ∣ Bs.relIndex V := by
    rintro ⟨m, hm⟩
    exact hk2 ⟨m, by rw [← hrel, hm]; ring⟩
  set Q : Subgroup G := Bs.map (MulAut.conj (l : G)).toMonoidHom with hQ
  have hQV : Q ≤ V := by
    rintro _ ⟨b, hb, rfl⟩
    show (l : G) * b * (l : G)⁻¹ ∈ V
    have hgN : (l : G) * b * (l : G)⁻¹ ∈ NL := mul_mem (mul_mem hlN (hBsN hb)) (inv_mem hlN)
    refine hmemV _ hgN (mul_mem (mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hb))
      (inv_mem (Subgroup.mem_sup_left l.2))) ?_
    have e1 : ggLAut L θ ⟨(l : G) * b * (l : G)⁻¹, hgN⟩ =
        MulAut.conj w * β ⟨b, hb⟩ * (MulAut.conj w)⁻¹ := by
      rw [← hlA, ggBeta_eq, ggLAut_conj]
      rfl
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp hw _).mp ⟨⟨b, hb⟩, rfl⟩
  have hQcard : Nat.card Q = Nat.card Bs :=
    Subgroup.card_map_of_injective (MulAut.conj (l : G)).injective
  have hidxQ : Q.relIndex V = Bs.relIndex V := by
    have h1 := Subgroup.relIndex_mul_card Q V
    rw [inf_eq_left.mpr hQV, hQcard, ← hidx] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hPp : IsPGroup p (Bs.subgroupOf V) :=
    (isPGroup_of_isElemAbelian hBs).of_equiv (Subgroup.subgroupOfEquivOfLe hBsV).symm
  have hQp : IsPGroup p (Q.subgroupOf V) :=
    ((isPGroup_of_isElemAbelian hBs).map (MulAut.conj (l : G)).toMonoidHom).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQV).symm
  have hpidxQ : ¬ p ∣ (Q.subgroupOf V).index := by
    change ¬ p ∣ Q.relIndex V
    rw [hidxQ]
    exact hpidx
  let SP : Sylow p ↥V := hPp.toSylow hpidx
  let SQ : Sylow p ↥V := hQp.toSylow hpidxQ
  obtain ⟨v, hv⟩ := MulAction.exists_smul_eq (↥V) SQ SP
  have hconjBs : ∀ b ∈ Bs, (v : G) * ((l : G) * b * (l : G)⁻¹) * (v : G)⁻¹ ∈ Bs := by
    intro b hb
    have hq : (⟨(l : G) * b * (l : G)⁻¹, hQV ⟨b, hb, rfl⟩⟩ : ↥V) ∈ (SQ : Subgroup ↥V) :=
      ⟨b, hb, rfl⟩
    have h2 := (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj v)).mpr hq
    rw [← Sylow.coe_subgroup_smul, hv] at h2
    exact h2
  set n : G := (v : G) * (l : G) with hn
  have hnN : n ∈ NL := mul_mem (hVN v.2) hlN
  have hnBs : n ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [mem_normalizer_iff_map_conj]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have e : (MulAut.conj n).toMonoidHom b =
          (v : G) * ((l : G) * b * (l : G)⁻¹) * (v : G)⁻¹ := by
        show n * b * n⁻¹ = _
        rw [hn]
        group
      rw [e]
      exact hconjBs b hb
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  refine ⟨n, hnN, hnBs, fun e he => ?_⟩
  have hA : ggLAut L θ ⟨n, hnN⟩ = ggLAut L θ ⟨v, hVN v.2⟩ * MulAut.conj w := by
    rw [← hlA, ← map_mul]
    rfl
  have hvE : ggLAut L θ ⟨v, hVN v.2⟩ ∈ β.range := hVE v v.2
  have hwe : MulAut.conj w * e * (MulAut.conj w)⁻¹ ∈ β.range :=
    (Subgroup.mem_normalizer_iff.mp hw e).mp he
  rw [hA]
  set u := ggLAut L θ ⟨v, hVN v.2⟩
  have hcomm := IsElemAbelian.comm hEhA hvE hwe
  calc u * MulAut.conj w * e * (u * MulAut.conj w)⁻¹ =
        u * (MulAut.conj w * e * (MulAut.conj w)⁻¹) * u⁻¹ := by group
    _ = (MulAut.conj w * e * (MulAut.conj w)⁻¹) * u * u⁻¹ := by rw [hcomm]
    _ = MulAut.conj w * e * (MulAut.conj w)⁻¹ := by group

end Lift

section Line

variable {G : Type} [Group G] [Finite G]

theorem not_normalizer_le_of_noInvariantLineTorus {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hline : GGNoInvariantLineTorus p r R I)
    {E : Subgroup G} (hEBs : E ≤ Bs) (hxE : x ∈ E)
    (hE : Nat.card E = p ^ 2) :
    ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  intro hN
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hC.2.1.1.trans hBsN
  obtain ⟨-, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  set β := ggBeta L θ hBsN with hβdef
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEBs.trans hBsN
  have hEA : IsElemAbelian p E := isElemAbelian_mono hBs.2.1 hEBs
  have hΛcard : Nat.card (ggBeta L θ hEN).range = p := by
    have h1 := card_range_ggBeta_mul_of hp hEA hxE hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hL θ hEN
    rw [hE, pow_two] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hΛE : (ggBeta L θ hEN).range ≤ β.range := range_ggBeta_le θ hEBs hEN hBsN
  have hle := Subgroup.card_le_of_le (range_ggBeta_le θ hBs.1 hBN hBsN)
  have hEhI : ((β.range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨c, rfl⟩
    exact ggBeta_mem L θ hBsN h3 c
  obtain ⟨hZ, hline'⟩ := hline β.range hEhI (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN)
    ((pow_le_card_range_ggBeta hp hS hL θ hBN hlift).trans hle) (h3'.trans hle)
  obtain ⟨w, hw, e, he, hne⟩ := hline' _ hΛE hΛcard
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center L) := by
    have h1 := hZ L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
    rwa [ker_ggQuotHom] at h1
  obtain ⟨n, hnL, hnBs, hact⟩ := exists_normalizer_lift hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
    hS.2.2.2.1.1 hS.2.2.2.2 hL θ hBsN hZ' w hw
  apply hne
  rw [← hact e (hΛE he)]
  obtain ⟨⟨e₀, he₀⟩, rfl⟩ := he
  have h1 : n * e₀ * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hN hnBs) e₀).mp he₀
  refine ⟨⟨n * e₀ * n⁻¹, h1⟩, ?_⟩
  rw [ggBeta_eq, ggBeta_eq, ggLAut_conj]
  rfl

end Line

theorem ggLNoInvariantLineInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I) :
    GGLNoInvariantLineInputOn S := by
  intro G _ _ p B Bs x L D J hC hM E hEBs hxE hE
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, hline⟩ :=
    largeEvenRawDatum_exists hraw
  exact not_normalizer_le_of_noInvariantLineTorus hC hL θ hBsN h3 hlift hline hEBs hxE hE

end CFSG.StandardType
