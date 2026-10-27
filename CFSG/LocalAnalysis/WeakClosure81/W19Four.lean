module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuAct
public import CFSG.LocalAnalysis.WeakClosure81.W19Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

namespace W19Aux

theorem sylow_normal_of_cyclic_of_lt {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    [Group.IsSolvable K] (hcore : CFSG.pPrimeCore p K = ⊥) (P : Sylow p K)
    (hnc : ¬ IsCyclic ↥(P : Subgroup K)) (hexp : ∀ x ∈ (P : Subgroup K), x ^ p = 1)
    {S : Subgroup K} (hS : Nat.Coprime p (Nat.card ↥S))
    (hmin : ∀ L : Subgroup K, S ≤ L → L < ⊤ → ∀ Q : Subgroup K, Q ≤ L → IsPGroup p Q →
      IsCyclic ↥Q) :
    (P : Subgroup K).Normal := by
  set N : Subgroup K := CFSG.pCore p K with hN
  haveI hNnormal : N.Normal := by rw [hN]; exact CFSG.pCore_normal
  have hNp : IsPGroup p N := by rw [hN]; exact CFSG.pCore_isPGroup
  have hchar : Subgroup.centralizer (N : Set K) ≤ N := by
    rw [hN]
    exact CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot K p hcore
      (CFSG.WholeGroup.layer_eq_bot_of_isSolvable)
  have hNP : N ≤ (P : Subgroup K) := hNp.le_sylow_of_normal P
  have hPN : (P : Subgroup K) ≤ N := by
    by_contra hnot
    have hNPne : N ≠ (P : Subgroup K) := fun h => hnot (le_of_eq h.symm)
    have hNltP : N < (P : Subgroup K) := lt_of_le_of_ne hNP hNPne
    have hcardlt : Nat.card ↥N < Nat.card ↥(P : Subgroup K) := Subgroup.card_lt_of_lt hNltP
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hNp
    have hNSbot : N ⊓ S = ⊥ := by
      have hcopNS : Nat.Coprime (Nat.card ↥N) (Nat.card ↥S) := by
        rw [hk]
        exact hS.pow_left k
      exact (Subgroup.disjoint_of_coprime_natCard hcopNS).eq_bot
    have hcardL : Nat.card ↥(N ⊔ S) = Nat.card ↥N * Nat.card ↥S := by
      have hset : ((N ⊔ S : Subgroup K) : Set K) = (N : Set K) * (S : Set K) :=
        Subgroup.normal_mul N S
      have hinj : Function.Injective (fun q : ↥N × ↥S => (q.1 : K) * (q.2 : K)) :=
        Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hNSbot)
      let f : ↥N × ↥S → ↥(N ⊔ S) := fun q =>
        ⟨(q.1 : K) * (q.2 : K),
          Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
      have hf : Function.Bijective f := by
        constructor
        · intro x y hxy
          exact hinj (congrArg Subtype.val hxy)
        · rintro ⟨z, hz⟩
          rw [← SetLike.mem_coe, hset] at hz
          obtain ⟨a, ha, b, hb, rfl⟩ := hz
          exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
      rw [← Nat.card_prod]
      exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
    have hLlt : N ⊔ S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      have hcardK : Nat.card K = Nat.card ↥N * Nat.card ↥S := by
        rw [← hcardL, htop, Subgroup.card_top]
      have hPdvd : Nat.card ↥(P : Subgroup K) ∣ Nat.card ↥N * Nat.card ↥S := by
        rw [← hcardK]
        exact Subgroup.card_subgroup_dvd_card (P : Subgroup K)
      have hcopPS : Nat.Coprime (Nat.card ↥(P : Subgroup K)) (Nat.card ↥S) := by
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 P.isPGroup'
        rw [hj]
        exact hS.pow_left j
      have hdvdN : Nat.card ↥(P : Subgroup K) ∣ Nat.card ↥N :=
        hcopPS.dvd_of_dvd_mul_right hPdvd
      have := Nat.le_of_dvd Nat.card_pos hdvdN
      omega
    have hNcyc : IsCyclic ↥N := hmin (N ⊔ S) le_sup_right hLlt N le_sup_left hNp
    obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top N).1 hNcyc
    have hgN : g ∈ N := hg ▸ Subgroup.mem_zpowers g
    have hgp : g ^ p = 1 := hexp g (hNP hgN)
    have hcardN : Nat.card ↥N = orderOf g := by rw [← hg, Nat.card_zpowers]
    have hdvd : Nat.card ↥N ∣ p := hcardN.symm ▸ orderOf_dvd_of_pow_eq_one hgp
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hpN
    · have hNbot : N = ⊥ := Subgroup.eq_bot_of_card_eq (H := N) h1
      have htop_le : (⊤ : Subgroup K) ≤ Subgroup.centralizer (N : Set K) := by
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        rw [hNbot] at hn
        change n ∈ (⊥ : Subgroup K) at hn
        rw [Subgroup.mem_bot] at hn
        subst hn
        simp
      have htriv : (⊤ : Subgroup K) ≤ ⊥ := htop_le.trans (hchar.trans (le_of_eq hNbot))
      haveI : Subsingleton K := ⟨fun a b => by
        have ha : a ∈ (⊥ : Subgroup K) := htriv trivial
        have hb : b ∈ (⊥ : Subgroup K) := htriv trivial
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
      haveI : Subsingleton ↥(P : Subgroup K) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
      exact hnc (isCyclic_of_subsingleton)
    · let f : K →* MulAut ↥N := MulAut.conjNormal (H := N)
      have hker_le : f.ker ≤ N := by
        intro x hx
        apply hchar
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        have hx1 : MulAut.conjNormal (H := N) x = 1 := MonoidHom.mem_ker.1 hx
        have hh := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : K)) hx1
        have h2 : x * n * x⁻¹ = n := by simpa [MulAut.conjNormal_apply] using hh
        exact (mul_inv_eq_iff_eq_mul.mp h2).symm
      have hker_le_p : Nat.card ↥f.ker ≤ p := by
        have := Subgroup.card_le_of_le hker_le
        rwa [hpN] at this
      haveI : IsCyclic ↥N := hNcyc
      have hrange_dvd : Nat.card ↥f.range ∣ p - 1 := by
        have h1 : Nat.card ↥f.range ∣ Nat.card (MulAut ↥N) := f.range.card_subgroup_dvd_card
        rw [IsCyclic.card_mulAut, hpN, Nat.totient_prime Fact.out] at h1
        exact h1
      have hcopP : Nat.Coprime (Nat.card ↥(P : Subgroup K)) (Nat.card ↥f.range) := by
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 P.isPGroup'
        rw [hj]
        have hp1 : Nat.Coprime p (p - 1) :=
          (Nat.coprime_self_sub_right (Fact.out : p.Prime).one_le).mpr (Nat.coprime_one_right p)
        exact (hp1.coprime_dvd_right hrange_dvd).pow_left j
      have hdvd : Nat.card ↥(P : Subgroup K) ∣ Nat.card ↥f.ker * Nat.card ↥f.range := by
        have h1 : Nat.card ↥(P : Subgroup K) ∣ Nat.card K :=
          Subgroup.card_subgroup_dvd_card (P : Subgroup K)
        rwa [← Subgroup.card_ker_mul_card_range f] at h1
      have hdvdker : Nat.card ↥(P : Subgroup K) ∣ Nat.card ↥f.ker :=
        hcopP.dvd_of_dvd_mul_right hdvd
      have hle := Nat.le_of_dvd Nat.card_pos hdvdker
      have hplt : p < Nat.card ↥(P : Subgroup K) := by omega
      omega
  have hPN' : (P : Subgroup K) = N := le_antisymm hPN hNP
  rw [hPN']
  exact hNnormal

end W19Aux

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem le_normalizer_sup_pCoreOf (c : MinCex193 D V₀ V p X) :
    X ⊔ D.T ≤ normalizer ((X ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) : Set G) := by
  classical
  haveI hp : Fact p.Prime := ⟨c.hyp.prime⟩
  let H : Subgroup G := X ⊔ D.T
  let R : Subgroup ↥H := CFSG.pCore 2 ↥H
  haveI hRnormal : R.Normal := CFSG.pCore_normal
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup
  let K := ↥H ⧸ R
  let π : ↥H →* K := QuotientGroup.mk' R
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hπker : π.ker = R := QuotientGroup.ker_mk' R
  let XH : Subgroup ↥H := X.subgroupOf H
  let TH : Subgroup ↥H := D.T.subgroupOf H
  let Xbar : Subgroup K := XH.map π
  let S : Subgroup K := TH.map π
  have hHsolv : Group.IsSolvable ↥H := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 c.hyp.isPGroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 D.sylowM.isPGroup
    have hcard : Nat.card ↥H = p ^ a * 2 ^ b := by
      change Nat.card ↥(X ⊔ D.T) = p ^ a * 2 ^ b
      rw [c.hyp.card_sup, ha, hb]
    exact CFSG.Quasithin.A312Ru.isSolvable_of_card_pq c.hyp.prime Nat.prime_two
      c.hyp.odd hcard
  haveI : Group.IsSolvable ↥H := hHsolv
  have hcoreK : CFSG.pPrimeCore p K = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro N hNnormal hNcop
    haveI : N.Normal := hNnormal
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 c.hyp.isPGroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 D.sylowM.isPGroup
    have hcardH : Nat.card ↥H = p ^ a * 2 ^ b := by
      change Nat.card ↥(X ⊔ D.T) = p ^ a * 2 ^ b
      rw [c.hyp.card_sup, ha, hb]
    have hN2 : IsPGroup 2 N := by
      have hNdvdH : Nat.card ↥N ∣ Nat.card ↥H := by
        have h1 : Nat.card ↥N ∣ Nat.card K := Subgroup.card_subgroup_dvd_card N
        have h2 : Nat.card K ∣ Nat.card ↥H := by
          change R.index ∣ Nat.card ↥H
          exact Subgroup.index_dvd_card R
        exact h1.trans h2
      rw [hcardH] at hNdvdH
      have hcopN : Nat.Coprime (Nat.card ↥N) (p ^ a) := hNcop.symm.pow_right a
      have hNdvd2 : Nat.card ↥N ∣ 2 ^ b :=
        hcopN.dvd_of_dvd_mul_right (by rwa [mul_comm] at hNdvdH)
      exact IsPGroup.of_card_dvd_pow hNdvd2
    have hcomap2 : IsPGroup 2 (N.comap π) :=
      hN2.comap_of_ker_isPGroup π (hπker.symm ▸ hR2)
    have hcomapN : (N.comap π).Normal := hNnormal.comap π
    have hle : N.comap π ≤ R := by
      change N.comap π ≤ CFSG.pCore 2 ↥H
      exact le_sSup ⟨hcomapN, hcomap2⟩
    have hmap : (N.comap π).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      rwa [hπker]
    rw [← Subgroup.map_comap_eq_self_of_surjective hπsurj N, hmap]
  have hS : Nat.Coprime p (Nat.card ↥S) := by
    have hTdvd : Nat.card ↥S ∣ Nat.card ↥D.T := by
      have h1 : Nat.card ↥S ∣ Nat.card ↥TH := Subgroup.card_map_dvd (H := TH) π
      have h2 : Nat.card ↥TH = Nat.card ↥D.T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show D.T ≤ H from le_sup_right)).toEquiv
      rwa [h2] at h1
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 D.sylowM.isPGroup
    have hdvd2 : Nat.card ↥S ∣ 2 ^ b := by rw [← hb]; exact hTdvd
    refine (c.hyp.prime.coprime_iff_not_dvd).2 fun hd => ?_
    have hp2 : p ∣ 2 := c.hyp.prime.dvd_of_dvd_pow (hd.trans hdvd2)
    exact c.hyp.odd ((Nat.prime_dvd_prime_iff_eq c.hyp.prime Nat.prime_two).1 hp2)
  let P : Sylow p K := ((c.hyp.isSylowIn_X).toSylow).mapSurjective hπsurj
  have hPcoe : (P : Subgroup K) = Xbar := by
    show ((c.hyp.isSylowIn_X).toSylow : Subgroup ↥H).map π = XH.map π
    rw [IsSylowIn.coe_toSylow]
  let ψ : ↥X →* ↥Xbar :=
    { toFun := fun x => ⟨π ⟨(x : G), Subgroup.mem_sup_left x.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(x : G), Subgroup.mem_sup_left x.2⟩,
          (Subgroup.mem_subgroupOf.mpr x.2), rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change π (1 : ↥H) = 1
        rw [map_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show π (⟨((x * y : ↥X) : G), Subgroup.mem_sup_left (x * y).2⟩ : ↥H)
          = π (⟨(x : G), Subgroup.mem_sup_left x.2⟩ : ↥H)
            * π (⟨(y : G), Subgroup.mem_sup_left y.2⟩ : ↥H)
        rw [show (⟨((x * y : ↥X) : G), Subgroup.mem_sup_left (x * y).2⟩ : ↥H)
            = (⟨(x : G), Subgroup.mem_sup_left x.2⟩ : ↥H)
              * ⟨(y : G), Subgroup.mem_sup_left y.2⟩ from Subtype.ext rfl, map_mul] }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hxy' : π (⟨(x : G), Subgroup.mem_sup_left x.2⟩ : ↥H)
        = π (⟨(y : G), Subgroup.mem_sup_left y.2⟩ : ↥H) := Subtype.ext_iff.mp hxy
    have hmemker : (⟨(x : G), Subgroup.mem_sup_left x.2⟩ : ↥H)
        * (⟨(y : G), Subgroup.mem_sup_left y.2⟩ : ↥H)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', mul_inv_cancel]
    rw [hπker] at hmemker
    have hval : (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 (X ⊔ D.T) := by
      have h1 : (((⟨(x : G), Subgroup.mem_sup_left x.2⟩ : ↥H)
          * (⟨(y : G), Subgroup.mem_sup_left y.2⟩ : ↥H)⁻¹ : ↥H) : G)
          ∈ pCoreOf 2 H :=
        Subgroup.mem_map.mpr ⟨_, hmemker, rfl⟩
      simpa using h1
    have hmemX : (x : G) * (y : G)⁻¹ ∈ X := X.mul_mem x.2 (X.inv_mem y.2)
    have hbot : X ⊓ pCoreOf 2 (X ⊔ D.T : Subgroup G) = ⊥ := c.hyp.inf_pCoreOf_eq_bot
    have hbot' : (x : G) * (y : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact ⟨hmemX, hval⟩
    rw [Subgroup.mem_bot] at hbot'
    exact Subtype.ext (mul_inv_eq_one.mp hbot')
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    have hwX : (w : G) ∈ X := Subgroup.mem_subgroupOf.mp hw
    refine ⟨⟨(w : G), hwX⟩, ?_⟩
    apply Subtype.ext
    show π (⟨(w : G), Subgroup.mem_sup_left hwX⟩ : ↥H) = z
    rw [show (⟨(w : G), Subgroup.mem_sup_left hwX⟩ : ↥H) = w from Subtype.ext rfl]
    exact hwz
  let e : ↥X ≃* ↥Xbar := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hncK : ¬ IsCyclic ↥(P : Subgroup K) := by
    rw [hPcoe]
    intro hcyc
    exact c.hyp.noncyclic (e.isCyclic.mpr hcyc)
  have hexpK : ∀ x ∈ (P : Subgroup K), x ^ p = 1 := by
    intro x hx
    rw [hPcoe] at hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
    change (π z) ^ p = 1
    rw [← map_pow]
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      simpa using c.hyp.exponent (z : G) hzX
    rw [hzp, map_one]
  have hminK : ∀ L : Subgroup K, S ≤ L → L < ⊤ →
      ∀ Q : Subgroup K, Q ≤ L → IsPGroup p Q → IsCyclic ↥Q := by
    intro L hSL hLlt Q hQL hQp
    set L' : Subgroup ↥H := L.comap π with hL'
    set L'' : Subgroup G := L'.map H.subtype with hL''
    have hTL' : TH ≤ L' := by
      intro t ht
      rw [Subgroup.mem_comap]
      exact hSL (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    have hTL'' : D.T ≤ L'' := by
      intro t ht
      have htH : t ∈ H := Subgroup.mem_sup_right ht
      refine Subgroup.mem_map.mpr ⟨⟨t, htH⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      exact hSL (Subgroup.mem_map.mpr ⟨⟨t, htH⟩,
        (Subgroup.mem_subgroupOf.mpr ht), rfl⟩)
    have hL''lt : L'' < H := by
      rw [lt_iff_le_not_ge]
      refine ⟨Subgroup.map_subtype_le _, ?_⟩
      intro hge
      have hL''top : L'' = H := le_antisymm (Subgroup.map_subtype_le _) hge
      have hL'top : L' = ⊤ := by
        apply Subgroup.map_subtype_inj.mp
        rw [← hL'', hL''top]
        ext x
        exact ⟨fun hx => ⟨⟨x, hx⟩, trivial, rfl⟩,
          fun hx => by obtain ⟨y, -, hy⟩ := hx; exact hy ▸ y.2⟩
      have hmaptop : L'.map π = L := by
        rw [hL']; exact Subgroup.map_comap_eq_self_of_surjective hπsurj L
      rw [hL'top, Subgroup.map_top_of_surjective π hπsurj] at hmaptop
      exact hLlt.ne hmaptop.symm
    set Q' : Subgroup ↥H := Q.comap π with hQ'
    have hQ'L' : Q' ≤ L' := by
      intro x hx
      rw [Subgroup.mem_comap] at hx ⊢
      exact hQL hx
    let g : ↥Q' →* ↥Q :=
      (π.comp Q'.subtype).codRestrict Q (fun x => Subgroup.mem_comap.mp x.2)
    have hgsurj : Function.Surjective g := by
      intro y
      obtain ⟨z, hz⟩ := hπsurj (y : K)
      refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
      rw [Subgroup.mem_comap, hz]; exact y.2
    obtain ⟨Q₁⟩ := Sylow.nonempty (p := p) (G := ↥Q')
    let QP : Sylow p ↥Q := Q₁.mapSurjective hgsurj
    have hQPtop : (QP : Subgroup ↥Q) = ⊤ := by
      have htop : IsPGroup p (⊤ : Subgroup ↥Q) := hQp.of_equiv Subgroup.topEquiv.symm
      exact (QP.is_maximal' htop le_top).symm
    have hQPimage : (Q₁ : Subgroup ↥Q').map g = ⊤ := by
      change (QP : Subgroup ↥Q) = ⊤
      exact hQPtop
    have hg₁surj : Function.Surjective (g.comp (Q₁ : Subgroup ↥Q').subtype) := by
      intro y
      have hy : y ∈ (Q₁ : Subgroup ↥Q').map g := by rw [hQPimage]; trivial
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, hxy⟩
    have hinj : Function.Injective (H.subtype.comp Q'.subtype) :=
      H.subtype_injective.comp Q'.subtype_injective
    let Q₁G : Subgroup G := (Q₁ : Subgroup ↥Q').map (H.subtype.comp Q'.subtype)
    have hQ₁G_le : Q₁G ≤ L'' := by
      dsimp only [Q₁G]
      rintro _ ⟨x, -, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Q'.subtype x, hQ'L' x.2, rfl⟩
    have hQ₁G_p : IsPGroup p Q₁G := Q₁.isPGroup'.map (H.subtype.comp Q'.subtype)
    have hcycQ₁G : IsCyclic ↥Q₁G := c.cyclic L'' hTL'' hL''lt Q₁G hQ₁G_le hQ₁G_p
    have hcycQ₁ : IsCyclic ↥Q₁ := by
      have heq := Subgroup.equivMapOfInjective (Q₁ : Subgroup ↥Q')
        (H.subtype.comp Q'.subtype) hinj
      exact heq.isCyclic.mpr hcycQ₁G
    haveI : IsCyclic ↥Q₁ := hcycQ₁
    exact isCyclic_of_surjective (g.comp (Q₁ : Subgroup ↥Q').subtype) hg₁surj
  have hXbarNormal : Xbar.Normal := by
    have hPnormal := W19Aux.sylow_normal_of_cyclic_of_lt hcoreK P hncK hexpK hS hminK
    rwa [hPcoe] at hPnormal
  have hXR : (X ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) = (Xbar.comap π).map H.subtype := by
    have h1 : Xbar.comap π = XH ⊔ R := by
      show (XH.map π).comap π = XH ⊔ R
      rw [Subgroup.comap_map_eq, hπker]
    rw [h1, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (le_sup_left : X ≤ H)]
    rfl
  rw [hXR]
  change H ≤ normalizer ((Xbar.comap π).map H.subtype : Set G)
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    subst hzy
    have hzbar : π z ∈ Xbar := Subgroup.mem_comap.mp hz
    let cH : ↥H := ⟨h, hh⟩ * z * ⟨h, hh⟩⁻¹
    have hcbar : π cH ∈ Xbar := by
      have := hXbarNormal.conj_mem (π z) hzbar (π ⟨h, hh⟩)
      simpa [cH, map_mul, map_inv] using this
    refine Subgroup.mem_map.mpr ⟨cH, ?_, ?_⟩
    · rw [Subgroup.mem_comap]; exact hcbar
    · show (cH : G) = h * (z : G) * h⁻¹
      simp only [cH, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have hzbar : π z ∈ Xbar := Subgroup.mem_comap.mp hz
    let w : ↥H := ⟨h, hh⟩⁻¹ * z * ⟨h, hh⟩
    have hwbar : π w ∈ Xbar := by
      have hthis := hXbarNormal.conj_mem (π z) hzbar ((π ⟨h, hh⟩)⁻¹)
      rw [inv_inv] at hthis
      simpa only [w, map_mul, map_inv] using hthis
    refine Subgroup.mem_map.mpr ⟨w, ?_, ?_⟩
    · rw [Subgroup.mem_comap]; exact hwbar
    · calc (w : G) = h⁻¹ * (z : G) * h := by
            simp only [w, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        _ = h⁻¹ * (h * y * h⁻¹) * h := congrArg (fun t : G => h⁻¹ * t * h) hzy
        _ = y := by group

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81
