module

public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6Step

public section

namespace CFSG.StandardType

open CFSG.Open


theorem ggB2der_exists_two_subgroup {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B L T : Subgroup G} {x : G} (hB : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hLperf : commutator ↥L = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hOut : ∀ φ : MulAut ↥L, ∃ l : ↥L, ∀ a : ↥L, φ a * (l * a * l⁻¹)⁻¹ ∈ Subgroup.center ↥L)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hT : T ≤ Subgroup.centralizer ({x} : Set G)) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) ∧
      ¬ U ≤ Subgroup.centralizer (L : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨x, hxB⟩)
  let C : Subgroup G :=
    Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({x} : Set G)
  have hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := by
    intro l hl c hc
    exact Subgroup.mem_centralizer_iff.mp hc.1 l hl
  have hdec : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ l ∈ L, ∃ c ∈ C, g = l * c := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (L : Set G) := hN hg
    have hmap : L.map (MulAut.conj g) = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    let φ : MulAut ↥L := ((MulAut.conj g).subgroupMap L).trans (MulEquiv.subgroupCongr hmap)
    have hφ : ∀ a : ↥L, (φ a : G) = g * (a : G) * g⁻¹ := by
      intro a
      simp [φ, MulAut.conj_apply]
    obtain ⟨l, hl⟩ := hOut φ
    have hψ_eq : ∀ a : ↥L, φ a = l * a * l⁻¹ := by
      let ψ : ↥L →* ↥L :=
        { toFun := fun a => φ a * (l * a * l⁻¹)⁻¹
          map_one' := by simp
          map_mul' := fun a b => by
            have hb : φ b * (l * b * l⁻¹)⁻¹ ∈ Subgroup.center ↥L := hl b
            have hcomm : (l * a * l⁻¹)⁻¹ * (φ b * (l * b * l⁻¹)⁻¹)
                = (φ b * (l * b * l⁻¹)⁻¹) * (l * a * l⁻¹)⁻¹ :=
              Subgroup.mem_center_iff.mp hb _
            calc φ (a * b) * (l * (a * b) * l⁻¹)⁻¹
                = φ a * φ b * ((l * b * l⁻¹)⁻¹ * (l * a * l⁻¹)⁻¹) := by
                  rw [map_mul]
                  congr 1
                  rw [show l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) by group,
                    mul_inv_rev]
              _ = φ a * ((φ b * (l * b * l⁻¹)⁻¹) * (l * a * l⁻¹)⁻¹) := by group
              _ = φ a * ((l * a * l⁻¹)⁻¹ * (φ b * (l * b * l⁻¹)⁻¹)) := by rw [hcomm]
              _ = φ a * (l * a * l⁻¹)⁻¹ * (φ b * (l * b * l⁻¹)⁻¹) := by group }
      have hker : commutator ↥L ≤ ψ.ker := by
        change ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ ψ.ker
        rw [Subgroup.commutator_le]
        intro a _ b _
        show ψ (a * b * a⁻¹ * b⁻¹) = 1
        simp only [map_mul, map_inv]
        have hcommab : ψ a * ψ b = ψ b * ψ a := Subgroup.mem_center_iff.mp (hl b) (ψ a)
        rw [hcommab]
        group
      have hψker : ψ.ker = ⊤ := top_le_iff.mp (hLperf ▸ hker)
      intro a
      have hmem : a ∈ ψ.ker := by rw [hψker]; exact Subgroup.mem_top a
      have h1 : ψ a = 1 := MonoidHom.mem_ker.mp hmem
      change φ a * (l * a * l⁻¹)⁻¹ = 1 at h1
      rwa [mul_inv_eq_one] at h1
    refine ⟨(l : G), l.2, (l : G)⁻¹ * g, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change (l : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 : g * y * g⁻¹ = (l : G) * y * (l : G)⁻¹ := by
          have h2 := congrArg (fun z : ↥L => (z : G)) (hψ_eq ⟨y, hy⟩)
          rw [hφ] at h2
          simpa using h2
        have h' : (l : G)⁻¹ * g * y = y * ((l : G)⁻¹ * g) := by
          calc (l : G)⁻¹ * g * y = (l : G)⁻¹ * (g * y * g⁻¹) * g := by group
            _ = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * g := by rw [h1]
            _ = y * ((l : G)⁻¹ * g) := by group
        exact h'.symm
      · change (l : G)⁻¹ * g ∈ Subgroup.centralizer ({x} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hlx : Commute (l : G) x := Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2)
        have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg
        exact ((hlx.inv_left.symm).mul_right hgx.symm).symm
    · group
  have hLinfC : ∀ z (hzL : z ∈ L), z ∈ C → (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    intro z hzL hzC
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    have hzC' : z ∈ Subgroup.centralizer (L : Set G) := hzC.1
    exact Subgroup.mem_centralizer_iff.mp hzC' (a : G) a.2
  have hZ0C : (Subgroup.center ↥L).map L.subtype ≤ C := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · change L.subtype w ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg (fun t : ↥L => (t : G)) (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩)
    · change L.subtype w ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx w.2)
  have hxC : x ∈ C := by
    refine ⟨?_, ?_⟩
    · change x ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hy)
    · change x ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
  let U : Subgroup G := ggProjLeft L C T hLC
  have hUL : U ≤ L := ggProjLeft_le_left
  have hU2 : IsPGroup 2 U := by
    intro u
    obtain ⟨huL, c, hcC, hucT⟩ := (mem_ggProjLeft).mp u.2
    obtain ⟨k, hk⟩ := hT2 ⟨(u : G) * c, hucT⟩
    have hkG : ((u : G) * c) ^ (2 ^ k) = 1 := by
      have := congrArg (fun z : ↥T => (z : G)) hk
      simpa using this
    have hcomm : Commute (u : G) c := hLC (u : G) huL c hcC
    have hupow : (u : G) ^ (2 ^ k) = (c ^ (2 ^ k))⁻¹ := by
      refine eq_inv_iff_mul_eq_one.mpr ?_
      rw [← hcomm.mul_pow (2 ^ k), hkG]
    have huLp : (u : G) ^ (2 ^ k) ∈ L := hUL (U.pow_mem u.2 (2 ^ k))
    have huCp : (u : G) ^ (2 ^ k) ∈ C := hupow.symm ▸ C.inv_mem (C.pow_mem hcC (2 ^ k))
    have hz : (⟨(u : G) ^ (2 ^ k), huLp⟩ : ↥L) ∈ Subgroup.center ↥L :=
      hLinfC _ huLp huCp
    obtain ⟨m, hm⟩ := hZ2 ⟨⟨(u : G) ^ (2 ^ k), huLp⟩, hz⟩
    have hmG : ((u : G) ^ (2 ^ k)) ^ (2 ^ m) = 1 := by
      have := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : G)) hm
      simpa using this
    refine ⟨k + m, ?_⟩
    apply Subtype.ext
    show (u : G) ^ (2 ^ (k + m)) = (1 : G)
    rw [pow_add, pow_mul]
    exact hmG
  have hconjC : ∀ b ∈ B, ∀ c ∈ C, b * c * b⁻¹ ∈ C := by
    intro b hb c hc
    refine ⟨?_, ?_⟩
    · change b * c * b⁻¹ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : b⁻¹ * y * b ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hBL (B.inv_mem hb)) y).mp hy
      have hcu : (b⁻¹ * y * b) * c = c * (b⁻¹ * y * b) :=
        Subgroup.mem_centralizer_iff.mp hc.1 (b⁻¹ * y * b) hy'
      calc y * (b * c * b⁻¹) = (b * (b⁻¹ * y * b)) * c * b⁻¹ := by group
        _ = b * ((b⁻¹ * y * b) * c) * b⁻¹ := by group
        _ = b * (c * (b⁻¹ * y * b)) * b⁻¹ := by rw [hcu]
        _ = (b * c * b⁻¹) * y := by group
    · change b * c * b⁻¹ ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hbx : Commute b x := Subgroup.mem_centralizer_singleton_iff.mp (hBx hb)
      have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      exact (hbx.mul_left hcx).mul_left hbx.inv_left
  have hconjU : ∀ b ∈ B, ∀ h ∈ U, b * h * b⁻¹ ∈ U := by
    intro b hb h hh
    exact conj_mem_ggProjLeft (hLC := hLC) (b := b)
      (fun l hl => (Subgroup.mem_normalizer_iff.mp (hBL hb) l).mp hl)
      (hconjC b hb)
      (fun t ht => (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht) hh
  have hBU : B ≤ Subgroup.normalizer (U : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconjU b hb h
    · intro hh
      have h' := hconjU b⁻¹ (B.inv_mem hb) (b * h * b⁻¹) hh
      have heq : b⁻¹ * (b * h * b⁻¹) * (b⁻¹)⁻¹ = h := by group
      rwa [heq] at h'
  have hUnc : ¬ U ≤ Subgroup.centralizer (L : Set G) := by
    intro hUc
    have hTC : T ≤ C := by
      intro t ht
      obtain ⟨l, hlL, c, hcC, hlc⟩ := hdec t (hT ht)
      have hlU : l ∈ U := (mem_ggProjLeft).mpr ⟨hlL, c, hcC, hlc ▸ ht⟩
      have hlC : l ∈ C := ⟨hUc hlU, hLx hlL⟩
      rw [hlc]
      exact C.mul_mem hlC hcC
    let Z0 : Subgroup G := (Subgroup.center ↥L).map L.subtype
    have hZ0_2 : IsPGroup 2 Z0 := hZ2.map L.subtype
    let P : Subgroup G := ggProjRight L C B hLC
    have hPC : P ≤ Subgroup.centralizer (L : Set G) := fun c hc => ((mem_ggProjRight).mp hc).1.1
    have hZ0P : Z0 ≤ P := by
      rintro z ⟨w, hw, rfl⟩
      exact (mem_ggProjRight).mpr
        ⟨hZ0C ⟨w, hw, rfl⟩, (w : G)⁻¹, L.inv_mem w.2, by simpa using B.one_mem⟩
    have hxP : x ∈ P :=
      (mem_ggProjRight).mpr ⟨hxC, 1, L.one_mem, by simpa using hxB⟩
    have hpowP : ∀ c ∈ P, c ^ p ∈ Z0 := by
      intro c hc
      obtain ⟨hcC, l, hlL, hlcB⟩ := (mem_ggProjRight).mp hc
      have hcomm : Commute l c := hLC l hlL c hcC
      have hbp : (l * c) ^ p = 1 := hB.2 (l * c) hlcB
      have hcp : c ^ p = (l ^ p)⁻¹ := by
        refine eq_inv_iff_mul_eq_one.mpr ?_
        have h1 : l ^ p * c ^ p = 1 := by rw [← hcomm.mul_pow p, hbp]
        have h2 : c ^ p * l ^ p = 1 := by
          rw [← hcomm.symm.mul_pow p]
          rw [show c * l = l * c from hcomm.symm]
          exact hbp
        exact h2
      have hcL : c ^ p ∈ L := hcp.symm ▸ L.inv_mem (L.pow_mem hlL p)
      have hcC' : c ^ p ∈ C := C.pow_mem hcC p
      exact Subgroup.mem_map_of_mem L.subtype (hLinfC (c ^ p) hcL hcC')
    have hxZ0 : x ∉ Z0 := by
      intro hxZ
      obtain ⟨n, hn⟩ := hZ0_2 ⟨x, hxZ⟩
      have hn' : x ^ (2 ^ n) = 1 := by
        have := congrArg (fun t : ↥Z0 => (t : G)) hn
        simpa using this
      have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn'
      have hxord : orderOf x = p := orderOf_eq_prime (hB.2 x hxB) hx1
      rw [hxord] at hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    let ZP : Subgroup ↥P := Z0.comap P.subtype
    have hZP2 : IsPGroup 2 ZP := hZ0_2.comap_of_injective P.subtype Subtype.coe_injective
    have hZPcenter : ZP ≤ Subgroup.center ↥P := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hzZ : (z : G) ∈ Z0 := hz
      obtain ⟨w, hw, hwz⟩ := hzZ
      have hwz' : (w : G) = (z : G) := hwz
      have hyw : (y : G) * (w : G) = (w : G) * (y : G) :=
        (Subgroup.mem_centralizer_iff.mp (hPC y.2) (w : G) w.2).symm
      calc (y : G) * (z : G) = (y : G) * (w : G) := by rw [hwz']
        _ = (w : G) * (y : G) := hyw
        _ = (z : G) * (y : G) := by rw [hwz']
    haveI : ZP.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h1 : n ∈ Subgroup.center ↥P := hZPcenter hn
      have h2 : g * n * g⁻¹ = n := by
        rw [Subgroup.mem_center_iff] at h1
        rw [h1 g]
        group
      rw [h2]
      exact hn
    have hQp : IsPGroup p (↥P ⧸ ZP) := by
      intro q
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective ZP q
      refine ⟨1, ?_⟩
      rw [pow_one, ← map_pow]
      exact (QuotientGroup.eq_one_iff (N := ZP) (c ^ p)).mpr (by
        change ((c : ↥P) : G) ^ p ∈ Z0
        exact hpowP (c : G) c.2)
    have hcop : Nat.Coprime (Nat.card ZP) ZP.index := by
      obtain ⟨n, hn⟩ := hZP2.exists_card_eq
      obtain ⟨m, hm⟩ := hQp.exists_card_eq
      rw [Subgroup.index_eq_card, hm, hn]
      exact Nat.coprime_pow_primes n m Nat.prime_two hp (Ne.symm hp2)
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
    have hKdisj : ZP ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
    have hKexp : ∀ k : K, k ^ p = 1 := by
      intro k
      have hkp : (k : ↥P) ^ p ∈ ZP := by
        change ((k : ↥P) : G) ^ p ∈ Z0
        exact hpowP (k : G) k.1.2
      have hmem : (k : ↥P) ^ p ∈ ZP ⊓ K := ⟨hkp, K.pow_mem k.2 p⟩
      rw [hKdisj, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hKp : IsPGroup p K := fun k => ⟨1, by rw [pow_one]; exact hKexp k⟩
    have hKcyc : IsCyclic K := by
      have hmap : K.map P.subtype ≤ Subgroup.centralizer (L : Set G) :=
        (Subgroup.map_subtype_le K).trans hPC
      have h1 : IsCyclic (K.map P.subtype) := hcyc (K.map P.subtype) hmap (hKp.map P.subtype)
      let e := Subgroup.equivMapOfInjective K P.subtype Subtype.coe_injective
      haveI : IsCyclic (K.map P.subtype) := h1
      exact isCyclic_of_surjective e.symm e.symm.surjective
    obtain ⟨w, hw, -⟩ := hK.existsUnique (⟨x, hxP⟩ : ↥P)
    obtain ⟨zx, kx⟩ := w
    have hzxk : (zx : ↥P) * (kx : ↥P) = (⟨x, hxP⟩ : ↥P) := hw
    have hkx_ne : kx ≠ 1 := by
      intro h1
      apply hxZ0
      have h2 : (zx : G) = x := by
        have h3 := congrArg (fun t : ↥P => (t : G)) hzxk
        rw [h1] at h3
        simpa using h3
      rw [← h2]
      exact zx.2
    have hcardK : Nat.card K = p := by
      haveI : IsCyclic K := hKcyc
      have hexp : Monoid.exponent K ∣ p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hKexp
      have hcard : Nat.card K ∣ p := by
        rwa [IsCyclic.exponent_eq_card] at hexp
      have hgt : 1 < Nat.card K := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact ⟨kx, 1, hkx_ne⟩
      rcases (Nat.dvd_prime hp).mp hcard with h | h
      · omega
      · exact h
    have hkx_ne' : (kx : ↥P) ≠ 1 := fun h => hkx_ne (Subtype.ext h)
    have hkorder : orderOf (kx : ↥P) = p := by
      have hkxp : (kx : ↥P) ^ p = 1 := by
        simpa using congrArg (fun t : K => (t : ↥P)) (hKexp kx)
      have hdvd : orderOf (kx : ↥P) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hkxp
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hkx_ne'
      · exact h
    have hKgen : K = Subgroup.zpowers (kx : ↥P) := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr kx.2)
      rw [Nat.card_zpowers, hkorder, hcardK]
    have hk_mem : (kx : G) ∈ Z0 ⊔ Subgroup.zpowers x := by
      have hk_eq : (kx : G) = (zx : G)⁻¹ * x := by
        have h3 : (zx : G) * (kx : G) = x := by
          simpa using congrArg (fun t : ↥P => (t : G)) hzxk
        rw [← h3]
        group
      rw [hk_eq]
      exact (Z0 ⊔ Subgroup.zpowers x).mul_mem
        (Subgroup.mem_sup_left (Z0.inv_mem (show (zx : G) ∈ Z0 from zx.2)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hPZ : P ≤ Z0 ⊔ Subgroup.zpowers x := by
      intro c hc
      obtain ⟨w, hw, -⟩ := hK.existsUnique (⟨c, hc⟩ : ↥P)
      obtain ⟨z, k⟩ := w
      have hzk : (z : ↥P) * (k : ↥P) = (⟨c, hc⟩ : ↥P) := hw
      have hkZ : (k : G) ∈ Z0 ⊔ Subgroup.zpowers x := by
        have hkmem : (k : ↥P) ∈ Subgroup.zpowers (kx : ↥P) := by
          rw [← hKgen]; exact k.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkmem
        have hkj : (k : G) = (kx : G) ^ j := by
          simpa using (congrArg (fun t : ↥P => (t : G)) hj).symm
        rw [hkj]
        exact (Z0 ⊔ Subgroup.zpowers x).zpow_mem hk_mem j
      have hc_eq : (c : G) = (z : G) * (k : G) := by
        simpa using (congrArg (fun t : ↥P => (t : G)) hzk).symm
      rw [hc_eq]
      exact (Z0 ⊔ Subgroup.zpowers x).mul_mem
        (Subgroup.mem_sup_left (show (z : G) ∈ Z0 from z.2)) hkZ
    have hTB1 : (⁅T, B⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨lb, hlbL, cb, hcbC, hb_eq⟩ := hdec b (hBx hb)
      have hcbP : cb ∈ P := (mem_ggProjRight).mpr ⟨hcbC, lb, hlbL, hb_eq ▸ hb⟩
      have hcbZ : cb ∈ Z0 ⊔ Subgroup.zpowers x := hPZ hcbP
      have htC : t ∈ C := hTC ht
      have hcomm_cb : cb * t = t * cb := by
        have h1 : Z0 ≤ Subgroup.centralizer ({t} : Set G) := by
          rintro z ⟨u, hu, rfl⟩
          change L.subtype u ∈ Subgroup.centralizer ({t} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp htC.1 (u : G) u.2
        have h2 : Subgroup.zpowers x ≤ Subgroup.centralizer ({t} : Set G) := by
          rw [Subgroup.zpowers_le]
          change x ∈ Subgroup.centralizer ({t} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp htC.2).symm
        exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le h1 h2) hcbZ)
      have hcomm_lb : lb * t = t * lb :=
        Subgroup.mem_centralizer_iff.mp htC.1 lb hlbL
      calc b * t = (lb * cb) * t := by rw [hb_eq]
        _ = lb * (cb * t) := by group
        _ = lb * (t * cb) := by rw [hcomm_cb]
        _ = (lb * t) * cb := by group
        _ = (t * lb) * cb := by rw [hcomm_lb]
        _ = t * (lb * cb) := by group
        _ = t * b := by rw [hb_eq]
    exact hTB hTB1
  exact ⟨U, hUL, hU2, hBU, hUnc⟩

end CFSG.StandardType

end
