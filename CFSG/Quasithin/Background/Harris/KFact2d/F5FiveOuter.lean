module

public import CFSG.Quasithin.Background.Harris.KFact2d.F5FiveKey
public import CFSG.Quasithin.Background.Harris.KFact2d.F5FiveModel
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_of_isSylowTwoOf'' {K S : Subgroup X} (h : IsSylowTwoOf S K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = S.subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsPGroup.toSylow (h.2.1.comap_subtype) h.2.2, rfl⟩

theorem zOf_eq_zpowers_of {K S : Subgroup X} (hSK : S ≤ K) {z : ↥K}
    (h : E2P.zOf (S.subgroupOf K) = Subgroup.zpowers z) :
    E2P.zOf S = Subgroup.zpowers (z : X) := by
  ext x
  constructor
  · intro hx
    have hxK : x ∈ K := hSK hx.1
    have h1 : (⟨x, hxK⟩ : ↥K) ∈ E2P.zOf (S.subgroupOf K) :=
      (mem_zOf_subgroupOf_iff hSK _).2 hx
    rw [h] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  · rintro ⟨k, rfl⟩
    have h1 : z ^ k ∈ E2P.zOf (S.subgroupOf K) := by
      rw [h]; exact Subgroup.zpow_mem_zpowers z k
    have := (mem_zOf_subgroupOf_iff hSK _).1 h1
    simpa using this

theorem outer_case
    {K S P : Subgroup X} (hK : IsPSU 3 5 1 ↥K) (hKn : K.Normal)
    (hcent : Subgroup.centralizer (K : Set X) = ⊥) (hS : IsSylowTwoOf S K)
    {u : X} (huu : u * u = 1) (huK : u ∉ K)
    (huC : ∀ c ∈ cenZ K S, u * c * u⁻¹ ∈ cenZ K S)
    (hS16 : Nat.card ↥S = 16) (hPC : P ≤ cenZ K S) (hSP : S ≤ P) (hSP' : S ≠ P)
    (hcomm : ∀ x ∈ P, u * x * u⁻¹ * x⁻¹ ∈ E2P.zOf S) : False := by
  have hCK : cenZ K S ≤ K := inf_le_left
  obtain ⟨hCcard, ⟨eL⟩⟩ := model_five hK hS
  obtain ⟨S', hS'⟩ := exists_sylow_of_isSylowTwoOf'' hS
  obtain ⟨z, -, hzS, hQ, hv⟩ := CFSG.Quasithin.Ch3E213M.OLA.kFactL3U3OuterInv_holds ↥K 5
    Nat.prime_five le_rfl (Or.inl ⟨by norm_num, hK⟩) S'
  rw [hS'] at hzS
  have hzX : E2P.zOf S = Subgroup.zpowers (z : X) := zOf_eq_zpowers_of hS.1 hzS
  set C := cenZ K S with hCdef
  have hzmem : (z : X) ∈ E2P.zOf S := hzX ▸ Subgroup.mem_zpowers _
  have hCcomm : ∀ c ∈ C, c * (z : X) = (z : X) * c := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp hc.2 _ hzmem).symm
  have hzC : (z : X) ∈ C := ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [hzX] at hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.refl (z : X)).zpow_left k).eq⟩
  have hu' : u⁻¹ = u := (eq_inv_of_mul_eq_one_left huu).symm
  let φ : ↥C →* ↥C :=
    { toFun := fun g => ⟨u * g * u⁻¹, huC g g.2⟩
      map_one' := by
        apply Subtype.ext
        show u * (1 : X) * u⁻¹ = 1
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show u * ((a : X) * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹)
        group }
  have hφ : ∀ g, φ (φ g) = g := by
    intro g
    apply Subtype.ext
    show u * (u * (g : X) * u⁻¹) * u⁻¹ = g
    rw [hu']
    calc u * (u * (g : X) * u) * u = (u * u) * g * (u * u) := by group
      _ = g := by rw [huu]; simp
  let ζ : ↥C := ⟨(z : X), hzC⟩
  have hζc : ∀ g : ↥C, g * ζ = ζ * g := fun g => Subtype.ext (hCcomm g g.2)
  have hzpow : ∀ y : ↥C, (y : X) ∈ Subgroup.zpowers (z : X) → y ∈ Subgroup.zpowers ζ := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [ζ] using hk)⟩
  let L : Subgroup ↥C := commutator ↥C
  have hLn : L.Normal := by
    show Subgroup.Normal (⁅(⊤ : Subgroup ↥C), ⊤⁆ : Subgroup ↥C)
    infer_instance
  have hL : Nat.card L = 120 := by
    rw [Nat.card_congr eL.toEquiv, card_sl2_five]
  have hφL : ∀ x ∈ L, φ x ∈ L := by
    have hle : L.map φ ≤ L := by
      show Subgroup.map φ ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ ⁅(⊤ : Subgroup ↥C), ⊤⁆
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact fun x hx => hle (Subgroup.mem_map_of_mem φ hx)
  have hcenC : ∀ y : ↥K, y ∈ Subgroup.centralizer ({z} : Set ↥K) → (y : X) ∈ C := by
    intro y hy
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [hzX] at hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hyz : (y : X) * (z : X) = (z : X) * y := by
      have := Subgroup.mem_centralizer_iff.mp hy z rfl
      exact congrArg Subtype.val this.symm
    have hc : Commute (z : X) (y : X) := hyz.symm
    exact (hc.zpow_left k).eq
  have hO2 : ∀ Q : Subgroup ↥C, Q.Normal → IsPGroup 2 Q → Q ≤ Subgroup.zpowers ζ := by
    intro Q hQn hQ2
    let ι : ↥C →* ↥K := Subgroup.inclusion hCK
    have hι : Function.Injective ι := Subgroup.inclusion_injective hCK
    have hQ0 : Q.map ι ≤ Subgroup.centralizer ({z} : Set ↥K) := by
      rintro _ ⟨q, -, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subtype.ext (hCcomm q q.2).symm
    have hQ02 : IsPGroup 2 ↥(Q.map ι) := hQ2.of_equiv (Subgroup.equivMapOfInjective Q ι hι)
    have hnorm : Subgroup.centralizer ({z} : Set ↥K) ≤ Subgroup.normalizer ((Q.map ι : Subgroup ↥K) : Set ↥K) := by
      intro y hy
      let ŷ : ↥C := ⟨(y : X), hcenC y hy⟩
      have hŷ : ι ŷ = y := rfl
      have conj : ∀ (c : ↥C) (h : ↥K), h ∈ Q.map ι → ι c * h * (ι c)⁻¹ ∈ Q.map ι := by
        rintro c h ⟨q, hq, rfl⟩
        exact ⟨c * q * c⁻¹, hQn.conj_mem q hq c, by simp⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => ?_, fun hh => ?_⟩
      · have := conj ŷ h hh
        rwa [hŷ] at this
      · have := conj ŷ⁻¹ _ hh
        have e : ι ŷ⁻¹ * (y * h * y⁻¹) * (ι ŷ⁻¹)⁻¹ = h := by
          rw [map_inv, ← hŷ]
          group
        rwa [e] at this
    have hle := hQ _ hQ0 hQ02 hnorm
    intro q hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_map_of_mem ι hq))
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun w : ↥K => (w : X)) hk
    have h5 : ((z : ↥K) : X) ^ k = ((ι q : ↥K) : X) := by simpa using this
    calc ((ζ ^ k : ↥C) : X) = (z : X) ^ k := by simp [ζ]
      _ = ((ι q : ↥K) : X) := h5
      _ = q := rfl
  have hP16 : 16 ∣ Nat.card (P.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, ← hS16]
    exact Subgroup.card_dvd_of_le hSP
  have hPbig : 16 < Nat.card (P.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, ← hS16]
    by_contra hle
    exact hSP' (Subgroup.eq_of_le_of_card_ge hSP (not_lt.mp hle))
  have hζP : ζ ∈ P.subgroupOf C := Subgroup.mem_subgroupOf.mpr (hSP hzmem.1)
  have hPfix : ∀ p ∈ P.subgroupOf C, φ p * p⁻¹ ∈ Subgroup.zpowers ζ := by
    intro p hp
    apply hzpow
    have hpP : (p : X) ∈ P := hp
    have := hcomm p hpP
    rw [hzX] at this
    exact this
  haveI := hLn
  have hall := keyLemma φ hφ ζ hζc hCcard L hL eL hφL hO2 (P.subgroupOf C) hP16 hPbig hζP hPfix
  have hφ_apply : ∀ g : ↥C, ((φ g : ↥C) : X) = u * g * u⁻¹ := fun g => rfl
  have hcommC : ∀ c ∈ C, u * c * u⁻¹ * c⁻¹ ∈ Subgroup.zpowers (z : X) := by
    intro c hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hall ⟨c, hc⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa [ζ, hφ_apply] using this
  let v : MulAut ↥K :=
    { toFun := fun k => ⟨u * k * u⁻¹, hKn.conj_mem k k.2 u⟩
      invFun := fun k => ⟨u⁻¹ * k * u, by simpa using hKn.conj_mem k k.2 u⁻¹⟩
      left_inv := fun k => by
        apply Subtype.ext
        show u⁻¹ * (u * (k : X) * u⁻¹) * u = k
        group
      right_inv := fun k => by
        apply Subtype.ext
        show u * (u⁻¹ * (k : X) * u) * u⁻¹ = k
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        show u * ((a : X) * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹)
        group }
  have hvv : v * v = 1 := by
    ext k
    show u * (u * (k : X) * u⁻¹) * u⁻¹ = k
    rw [hu']
    calc u * (u * (k : X) * u) * u = (u * u) * k * (u * u) := by group
      _ = k := by rw [huu]; simp
  have hvne : v ≠ 1 := by
    intro h
    have hu : u ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := congrArg (fun w : MulAut ↥K => ((w ⟨y, hy⟩ : ↥K) : X)) h
      have h2 : u * y * u⁻¹ = y := this
      calc y * u = (u * y * u⁻¹) * u := by rw [h2]
        _ = u * y := by group
    rw [hcent, Subgroup.mem_bot] at hu
    exact huK (hu ▸ K.one_mem)
  have hord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hvne
  have hyp : ∀ x ∈ Subgroup.centralizer ({z} : Set ↥K), v x * x⁻¹ ∈ Subgroup.zpowers z := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcommC x (hcenC x hx))
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simpa using hk.symm ▸ rfl
  obtain ⟨k, hk⟩ := hv v hord hyp
  have hcu : (k : X)⁻¹ * u ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := congrArg (fun w : MulAut ↥K => ((w ⟨y, hy⟩ : ↥K) : X)) hk
    have h3 : (k : X) * y * (k : X)⁻¹ = u * y * u⁻¹ := h2
    have h4 : u * y = (k : X) * y * (k : X)⁻¹ * u := by rw [h3]; group
    calc y * ((k : X)⁻¹ * u) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹ * u) := by group
      _ = (k : X)⁻¹ * (u * y) := by rw [← h4]
      _ = ((k : X)⁻¹ * u) * y := by group
  rw [hcent, Subgroup.mem_bot, inv_mul_eq_one] at hcu
  exact huK (hcu ▸ k.2)

end CFSG.Quasithin.Background.Harris.KFact2d
