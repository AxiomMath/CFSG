module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.CentralS3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace F53

open Equiv

theorem perm3_card_eq_two_of_isPGroup (P : Subgroup (Perm (Fin 3))) (hP : IsPGroup 2 P)
    (hne : P ≠ ⊥) : Nat.card P = 2 := by
  have h1 : 1 < Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hne
  have h2 := perm3_card_le_two_of_isPGroup P hP
  omega

theorem perm3_eq_top_of_normal (N P : Subgroup (Perm (Fin 3))) [N.Normal] (hP : IsPGroup 2 P)
    (hPN : P ≤ N) (hne : P ≠ ⊥) : N = ⊤ := by
  have hP2 := perm3_card_eq_two_of_isPGroup P hP hne
  have hN : N ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hPN))
  have hA := normal_ge_alt3 N hN
  have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 3)
    rw [Nat.card_perm] at h
    have e : Nat.card (Fin 3) = 3 := by simp
    rw [e] at h
    rw [show Nat.factorial 3 = 6 from rfl] at h
    omega
  have hd2 : 2 ∣ Nat.card N := hP2 ▸ Subgroup.card_dvd_of_le hPN
  have hd3 : 3 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hA
    rwa [h3] at this
  have hdvd : Nat.card N ∣ 6 := card_perm3 ▸ Subgroup.card_subgroup_dvd_card N
  have h6 : Nat.card N = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card N := Nat.card_pos
    obtain ⟨a, ha⟩ := hd2
    obtain ⟨b, hb⟩ := hd3
    omega
  exact Subgroup.eq_top_of_card_eq _ (by rw [h6, card_perm3])

section Abstract

variable {A : Type*} [Group A]

theorem comm_normalClosure_le (Q B : Subgroup A) [hQ : Q.Normal] [hN : (Q ⊓ B).Normal]
    (hcomm : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ * q⁻¹ ∈ B) :
    ∀ g ∈ Subgroup.normalClosure (B : Set A), ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ Q ⊓ B := by
  let C : Subgroup A :=
    { carrier := {g | ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ Q ⊓ B}
      one_mem' := fun q _ => by simp
      mul_mem' := by
        intro g₁ g₂ h₁ h₂ q hq
        have e : g₁ * g₂ * q * (g₁ * g₂)⁻¹ * q⁻¹ =
            (g₁ * (g₂ * q * g₂⁻¹ * q⁻¹) * g₁⁻¹) * (g₁ * q * g₁⁻¹ * q⁻¹) := by group
        rw [e]
        exact (Q ⊓ B).mul_mem (hN.conj_mem _ (h₂ q hq) g₁) (h₁ q hq)
      inv_mem' := by
        intro g hg q hq
        have hq' : g⁻¹ * q * g ∈ Q := by
          have := hQ.conj_mem q hq g⁻¹
          simpa using this
        have h := hg _ hq'
        have e : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ = (g * (g⁻¹ * q * g) * g⁻¹ * (g⁻¹ * q * g)⁻¹)⁻¹ := by
          group
        rw [e]
        exact (Q ⊓ B).inv_mem h }
  have hCn : C.Normal := by
    constructor
    intro g hg h q hq
    have hq' : h⁻¹ * q * h ∈ Q := by
      have := hQ.conj_mem q hq h⁻¹
      simpa using this
    have e : h * g * h⁻¹ * q * (h * g * h⁻¹)⁻¹ * q⁻¹ =
        h * (g * (h⁻¹ * q * h) * g⁻¹ * (h⁻¹ * q * h)⁻¹) * h⁻¹ := by group
    rw [e]
    exact hN.conj_mem _ (hg _ hq') h
  have hBC : (B : Set A) ⊆ C := by
    intro b hb q hq
    have h1 := hcomm b hb q hq
    refine ⟨?_, h1⟩
    have := hQ.conj_mem q hq b
    exact Q.mul_mem this (Q.inv_mem hq)
  exact fun g hg => Subgroup.normalClosure_le_normal hBC hg

theorem normalClosure_map_eq_top [Finite A] (ψ : A →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (B : Subgroup A) (hB2 : IsPGroup 2 B) (hBQ : ¬ B ≤ ψ.ker) :
    (Subgroup.normalClosure (B : Set A)).map ψ = ⊤ := by
  have : ((Subgroup.normalClosure (B : Set A)).map ψ).Normal :=
    Subgroup.Normal.map inferInstance ψ hψ
  obtain ⟨g, hg, hgψ⟩ := Set.not_subset.mp hBQ
  have hP : IsPGroup 2 (B.map ψ) := hB2.map ψ
  have hne : B.map ψ ≠ ⊥ := by
    intro h
    apply hgψ
    have : ψ g ∈ B.map ψ := ⟨g, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  exact perm3_eq_top_of_normal _ _ hP (Subgroup.map_mono Subgroup.le_normalClosure) hne

theorem normalClosure_inf_ker_le [Finite A] (ψ : A →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (B : Subgroup A) (hB2 : IsPGroup 2 B) (hQ2 : IsPGroup 2 ψ.ker) (hBQ : ¬ B ≤ ψ.ker)
    (hcomm : ∀ b ∈ B, ∀ q ∈ ψ.ker, b * q * b⁻¹ * q⁻¹ ∈ B) (hN : (ψ.ker ⊓ B).Normal) :
    Subgroup.normalClosure (B : Set A) ⊓ ψ.ker ≤ B := by
  set L := Subgroup.normalClosure (B : Set A) with hL
  set N : Subgroup A := ψ.ker ⊓ B with hNdef
  have hBL : B ≤ L := Subgroup.le_normalClosure
  have hb := comm_normalClosure_le ψ.ker B hcomm
  have htop := normalClosure_map_eq_top ψ hψ B hB2 hBQ
  have hdec : ∀ x : A, ∃ l ∈ L, ∃ q ∈ ψ.ker, x = l * q := by
    intro x
    have : ψ x ∈ L.map ψ := by rw [htop]; trivial
    obtain ⟨l, hl, hlx⟩ := this
    refine ⟨l, hl, l⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
  obtain ⟨g₀, hg₀B, hg₀Q⟩ := Set.not_subset.mp hBQ
  have hg₀ψ : ψ g₀ ≠ 1 := hg₀Q
  have hBψ : Nat.card (B.map ψ) = 2 := by
    refine perm3_card_eq_two_of_isPGroup _ (hB2.map ψ) ?_
    intro h
    have : ψ g₀ ∈ B.map ψ := ⟨g₀, hg₀B, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hg₀ψ this
  have hψeq : ∀ b ∈ B, ψ b ≠ 1 → ψ b = ψ g₀ := by
    intro b hbB hbψ
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : B.map ψ)).mp hBψ
    have h1 := hy ⟨ψ b, ⟨b, hbB, rfl⟩⟩ (fun h => hbψ (congrArg Subtype.val h))
    have h2 := hy ⟨ψ g₀, ⟨g₀, hg₀B, rfl⟩⟩ (fun h => hg₀ψ (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hψsq : ∀ b ∈ B, ψ b ^ 2 = 1 := by
    intro b hbB
    have := pow_card_eq_one' (G := B.map ψ) (x := ⟨ψ b, ⟨b, hbB, rfl⟩⟩)
    rw [hBψ] at this
    exact congrArg Subtype.val this
  have hNn : N.Normal := hN
  let Nl : Subgroup ↥L := N.subgroupOf L
  have hNl : Nl.Normal := inferInstance
  let φ : ↥L →* Perm (Fin 3) := ψ.comp L.subtype
  have hNφ : Nl ≤ φ.ker := fun x hx => (MonoidHom.mem_ker.mpr ((MonoidHom.mem_ker.mp hx.1)))
  let ρ : (↥L ⧸ Nl) →* Perm (Fin 3) := QuotientGroup.lift Nl φ hNφ
  have hρ : ∀ x : ↥L, ρ (QuotientGroup.mk x) = ψ x := fun x => rfl
  have hker : ∀ x : ↥L, ρ (QuotientGroup.mk x) = 1 ↔ (x : A) ∈ ψ.ker := fun x => by
    rw [hρ]; rfl
  have hρsurj : Function.Surjective ρ := by
    intro σ
    have : σ ∈ L.map ψ := by rw [htop]; trivial
    obtain ⟨l, hl, hlσ⟩ := this
    exact ⟨QuotientGroup.mk ⟨l, hl⟩, by rw [hρ]; exact hlσ⟩
  have hρker : ∀ z ∈ ρ.ker, ∃ x : ↥L, (x : A) ∈ ψ.ker ∧ QuotientGroup.mk x = z := by
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨x, (hker x).mp hz, rfl⟩
  have hZc : ρ.ker ≤ Subgroup.center (↥L ⧸ Nl) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hρker z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have h1 := hb (l⁻¹ : ↥L) (l⁻¹ : ↥L).2 (x : A) hx
    have h2 := hNn.conj_mem _ h1 ((x : A)⁻¹)
    have e : (((l * x)⁻¹ * (x * l) : ↥L) : A) =
        (x : A)⁻¹ * ((l : A)⁻¹ * x * ((l : A)⁻¹)⁻¹ * (x : A)⁻¹) * ((x : A)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]; exact h2
  have hZ2 : IsPGroup 2 ρ.ker := by
    intro z
    obtain ⟨x, hx, hxz⟩ := hρker z.1 z.2
    obtain ⟨k, hk⟩ := hQ2 ⟨(x : A), hx⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (z.1) ^ (2 ^ k) = 1
    rw [← hxz, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    have hk' : (x : A) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    congr 1
    exact Subtype.ext (by simpa using hk')
  have hg₀L : g₀ ∈ L := hBL hg₀B
  let u : ↥L ⧸ Nl := QuotientGroup.mk ⟨g₀, hg₀L⟩
  have hu2 : u ^ 2 = 1 := by
    show (QuotientGroup.mk ⟨g₀, hg₀L⟩ : ↥L ⧸ Nl) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨MonoidHom.mem_ker.mpr (by show ψ (g₀ ^ 2) = 1; rw [map_pow]; exact hψsq g₀ hg₀B),
      B.pow_mem hg₀B 2⟩
  have hu : ρ u ≠ 1 := by
    show ρ (QuotientGroup.mk ⟨g₀, hg₀L⟩) ≠ 1
    rw [hρ]; exact hg₀ψ
  have hgen : Subgroup.normalClosure ({u} : Set (↥L ⧸ Nl)) = ⊤ := by
    set M := Subgroup.normalClosure ({u} : Set (↥L ⧸ Nl)) with hM
    have hMn : M.Normal := inferInstance
    have hmkB : ∀ b (hb' : b ∈ B), (QuotientGroup.mk ⟨b, hBL hb'⟩ : ↥L ⧸ Nl) ∈ M := by
      intro b hb'
      by_cases hbQ : b ∈ ψ.ker
      · have : (QuotientGroup.mk ⟨b, hBL hb'⟩ : ↥L ⧸ Nl) = 1 := by
          rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact ⟨hbQ, hb'⟩
        rw [this]; exact M.one_mem
      · have h := hψeq b hb' hbQ
        have : (QuotientGroup.mk ⟨b, hBL hb'⟩ : ↥L ⧸ Nl) = u := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          refine ⟨MonoidHom.mem_ker.mpr ?_, B.mul_mem (B.inv_mem hb') hg₀B⟩
          show ψ (b⁻¹ * g₀) = 1
          rw [map_mul, map_inv, h, inv_mul_cancel]
        rw [this]; exact Subgroup.subset_normalClosure rfl
    let S : Subgroup A := (M.comap (QuotientGroup.mk' Nl)).map L.subtype
    have hLS : L ≤ S := by
      refine (Subgroup.closure_le S).mpr ?_
      intro x hx
      obtain ⟨b, hbB, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have hxL : x ∈ L := Subgroup.conjugatesOfSet_subset_normalClosure hx
      obtain ⟨l, hl, q, hq, hcd⟩ := hdec c
      have hnN : q * b * q⁻¹ * b⁻¹ ∈ N := by
        have h1 := hb b (hBL hbB) q hq
        have e : q * b * q⁻¹ * b⁻¹ = (b * q * b⁻¹ * q⁻¹)⁻¹ := by group
        rw [e]; exact N.inv_mem h1
      have hln : l * (q * b * q⁻¹ * b⁻¹) * l⁻¹ ∈ N := hNn.conj_mem _ hnN l
      have hlnL : l * (q * b * q⁻¹ * b⁻¹) * l⁻¹ ∈ L := hBL hln.2
      have key : (⟨x, hxL⟩ : ↥L) = ⟨l * (q * b * q⁻¹ * b⁻¹) * l⁻¹, hlnL⟩ *
          (⟨l, hl⟩ * ⟨b, hBL hbB⟩ * ⟨l, hl⟩⁻¹) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hc, hcd]; group
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      show (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ Nl) ∈ M
      rw [key, QuotientGroup.mk_mul]
      have h1 : (QuotientGroup.mk ⟨l * (q * b * q⁻¹ * b⁻¹) * l⁻¹, hlnL⟩ : ↥L ⧸ Nl) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hln
      rw [h1, one_mul]
      have := hMn.conj_mem _ (hmkB b hbB) (QuotientGroup.mk ⟨l, hl⟩)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact this
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨y', hy', hyx⟩ := hLS x.2
    have : y' = x := Subtype.ext hyx
    rw [this] at hy'
    exact hy'
  have hZ := central_extension_S3_normalClosure ρ.ker hZc hZ2 ρ hρsurj rfl u hu2 hu hgen
  intro x ⟨hxL, hxQ⟩
  have h1 : ρ (QuotientGroup.mk ⟨x, hxL⟩) = 1 := (hker _).mpr hxQ
  have h2 : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ Nl) ∈ ρ.ker := h1
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h2
  exact h2.2

theorem not_two_dvd_index_normalClosure [Finite A] (ψ : A →* Perm (Fin 3))
    (hψ : Function.Surjective ψ) (B : Subgroup A) (hB2 : IsPGroup 2 B) (hBQ : ¬ B ≤ ψ.ker)
    (hle : Subgroup.normalClosure (B : Set A) ⊓ ψ.ker ≤ B) :
    ¬ 2 ∣ (B.subgroupOf (Subgroup.normalClosure (B : Set A))).index := by
  set L := Subgroup.normalClosure (B : Set A) with hL
  have htop := normalClosure_map_eq_top ψ hψ B hB2 hBQ
  let φ : ↥L →* Perm (Fin 3) := ψ.comp L.subtype
  have hφ : Function.Surjective φ := by
    intro σ
    have : σ ∈ L.map ψ := by rw [htop]; trivial
    obtain ⟨l, hl, rfl⟩ := this
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : φ.ker ≤ B.subgroupOf L := fun x hx => hle ⟨x.2, hx⟩
  have h1 := Subgroup.index_map_eq (B.subgroupOf L) hφ hker
  obtain ⟨g₀, hg₀B, hg₀Q⟩ := Set.not_subset.mp hBQ
  have hP : IsPGroup 2 ((B.subgroupOf L).map φ) := (hB2.comap_subtype).map φ
  have hne : (B.subgroupOf L).map φ ≠ ⊥ := by
    intro h
    have hg₀L : g₀ ∈ L := Subgroup.le_normalClosure hg₀B
    have : φ ⟨g₀, hg₀L⟩ ∈ (B.subgroupOf L).map φ := ⟨⟨g₀, hg₀L⟩, hg₀B, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hg₀Q this
  have hcard := perm3_card_eq_two_of_isPGroup _ hP hne
  have h6 := ((B.subgroupOf L).map φ).card_mul_index
  rw [card_perm3, h1, hcard] at h6
  omega

theorem abstract_S3 [Finite A] (ψ : A →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (B : Subgroup A) (hB2 : IsPGroup 2 B) (hQ2 : IsPGroup 2 ψ.ker) (hBQ : ¬ B ≤ ψ.ker)
    (hcomm : ∀ b ∈ B, ∀ q ∈ ψ.ker, b * q * b⁻¹ * q⁻¹ ∈ B) (hN : (ψ.ker ⊓ B).Normal) :
    Subgroup.normalClosure (B : Set A) ⊓ ψ.ker ≤ B ∧
      Subgroup.normalClosure (B : Set A) ⊔ ψ.ker = ⊤ ∧
      ¬ 2 ∣ (B.subgroupOf (Subgroup.normalClosure (B : Set A))).index := by
  have hle := normalClosure_inf_ker_le ψ hψ B hB2 hQ2 hBQ hcomm hN
  refine ⟨hle, ?_, not_two_dvd_index_normalClosure ψ hψ B hB2 hBQ hle⟩
  have htop := normalClosure_map_eq_top ψ hψ B hB2 hBQ
  rw [eq_top_iff]
  intro x _
  have : ψ x ∈ (Subgroup.normalClosure (B : Set A)).map ψ := by rw [htop]; trivial
  obtain ⟨l, hl, hlx⟩ := this
  have : x = l * (l⁻¹ * x) := by group
  rw [this]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ?_)
  rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]

end Abstract

end F53

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss27S3At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (h28 : Hss28At H M) :
    Hss27S3At H M := by
  intro hb α β hαβ hv hα hY
  by_contra hn
  have hβn : β ∈ nbrs α := hαβ
  have hαn : α ∈ nbrs β := hαβ.symm
  have hbB : 2 ≤ bAt β := hb.trans (bMin_le_bAt β)
  have hCQ : stab α ⊓ Subgroup.centralizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) = Qv α ⊓ Qv β := by
    apply le_antisymm
    · rintro x ⟨hxs, hxc⟩
      have hxZα : x ∈ stab α ⊓ Subgroup.centralizer (Zv α : Set G) :=
        ⟨hxs, Subgroup.centralizer_le (fun z hz => Subgroup.mem_sup_left hz) hxc⟩
      rw [centralizer_Zv_eq_Qv_of_bAt hA hα] at hxZα
      refine ⟨hxZα, ?_⟩
      have hxsβ : x ∈ stab β := Qv_le_stab_of_mem_nbrs hA hβn hxZα
      have hxZβ : x ∈ stab β ⊓ Subgroup.centralizer (Zv β : Set G) :=
        ⟨hxsβ, Subgroup.centralizer_le (fun z hz => Subgroup.mem_sup_right hz) hxc⟩
      rcases centralizer_Zv_dichotomy hA β with h | h
      · rw [h] at hxZβ; exact hxZβ
      · exact absurd (h ▸ omegaOneCenter_le_centerOf_self (stab β)) hn
    · rintro x ⟨hxα, hxβ⟩
      refine ⟨pCoreOf_le 2 _ hxα, ?_⟩
      have hle : (Zv α ⊔ Zv β : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le ?_ ?_
        · intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 x hxα))
        · intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hz).2 x hxβ))
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) x rfl).symm
  have hNnorm : stab α ≤ Subgroup.normalizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) := by
    rw [← hCQ]; exact SitSigma.normalizer_inf_centralizer hY
  have hZβQα : Zv β ≤ Qv α :=
    Zv_le_Qv_of_dist_lt (by rw [dist_eq_one_iff_adj.mpr hαβ.symm]; omega)
  have hq := h28 (by omega) α β hαβ hα
  have hnQ : ¬ Qv β ≤ Qv α := by
    intro h
    have h1 : Qv α = stab α ⊓ stab β := by rw [← hq]; exact (sup_eq_left.mpr h).symm
    have := relIndex_Qv_inf_true hA hβn hv
    rw [← h1, Subgroup.relIndex_self] at this
    omega
  have hBle : Qv β ≤ stab α := Qv_le_stab_of_mem_nbrs hA hαn
  obtain ⟨ψ, hψ, hker⟩ := exists_quotHom_true hA hv
  have hψk : ψ.ker = (Qv α).subgroupOf (stab α) := by
    ext x; rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set B : Subgroup ↥(stab α) := (Qv β).subgroupOf (stab α) with hBdef
  have hB2 : IsPGroup 2 B := (pCoreOf_isPGroup (r := 2) (stab β)).comap_subtype
  have hQ2 : IsPGroup 2 ψ.ker := by
    rw [hψk]; exact (pCoreOf_isPGroup (r := 2) (stab α)).comap_subtype
  have hBQ : ¬ B ≤ ψ.ker := by
    intro h
    apply hnQ
    intro x hx
    have := h (show (⟨x, hBle hx⟩ : ↥(stab α)) ∈ B from hx)
    rw [hψk] at this
    exact this
  have hcomm : ∀ b ∈ B, ∀ q ∈ ψ.ker, b * q * b⁻¹ * q⁻¹ ∈ B := by
    intro b hb' q hq
    rw [hψk] at hq
    have hqs : (q : G) ∈ stab β := Qv_le_stab_of_mem_nbrs hA hβn hq
    have h1 : (q : G) * (b : G)⁻¹ * (q : G)⁻¹ ∈ Qv β :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab β) hqs) _).mp
        ((Qv β).inv_mem hb')
    show ((b * q * b⁻¹ * q⁻¹ : ↥(stab α)) : G) ∈ Qv β
    have e : ((b * q * b⁻¹ * q⁻¹ : ↥(stab α)) : G) =
        (b : G) * ((q : G) * (b : G)⁻¹ * (q : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact (Qv β).mul_mem hb' h1
  have hN : (ψ.ker ⊓ B).Normal := by
    constructor
    intro n hn' g
    have hn2 : (n : G) ∈ Qv α ⊓ Qv β := by
      rw [hψk] at hn'
      exact ⟨hn'.1, hn'.2⟩
    have := (Subgroup.mem_normalizer_iff.mp (hNnorm g.2) _).mp hn2
    rw [hψk]
    exact this
  obtain ⟨hle, hgenL, hind⟩ := abstract_S3 ψ hψ B hB2 hQ2 hBQ hcomm hN
  set L : Subgroup ↥(stab α) := Subgroup.normalClosure (B : Set ↥(stab α)) with hL
  set U : Subgroup G := L.map (stab α).subtype with hU
  have hBL : B ≤ L := Subgroup.le_normalClosure
  have hQβU : Qv β ≤ U := fun x hx => ⟨⟨x, hBle hx⟩, hBL (show (⟨x, hBle hx⟩ : ↥(stab α)) ∈ B from hx), rfl⟩
  have hUs : U ≤ stab α := Subgroup.map_subtype_le L
  have hsyl : IsSylowTwoOf (Qv β ⊓ U) U := by
    rw [inf_eq_left.mpr hQβU]
    refine ⟨hQβU, pCoreOf_isPGroup 2 _, ?_⟩
    have h1 : (Qv β).relIndex U = B.relIndex L := by
      have e1 : B.map (stab α).subtype = Qv β := Subgroup.map_subgroupOf_eq_of_le hBle
      rw [← e1, hU, Subgroup.relIndex_map_map_of_injective _ _ (stab α).subtype_injective]
    have h2 : ((Qv β).subgroupOf U).index = (B.subgroupOf L).index := h1
    rw [h2]; exact hind
  have hzle : Zv β ≤ pCoreOf 2 U := by
    refine le_trans (le_inf hZβQα ((Zv_le_Qv hA β).trans hQβU)) (pCoreOf_inf_le hUs)
  have hgen : U ⊔ (stab α ⊓ stab β) = stab α := by
    apply le_antisymm (sup_le hUs inf_le_left)
    have h1 : (L ⊔ ψ.ker).map (stab α).subtype = stab α := by
      rw [hgenL, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_sup, hψk, Subgroup.map_subgroupOf_eq_of_le
      (show Qv α ≤ stab α from pCoreOf_le 2 _)] at h1
    exact h1.symm.le.trans (sup_le_sup_left (Qv_le_edge hA hβn) _)
  have hsit : SitSigma α β U := ⟨hαβ, hUs, hsyl, hzle, hgen⟩
  have hZα := h26 (by omega) α β U hsit hQβU
  have hcen : stab α ≤ Subgroup.centralizer (Zv α : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz'
    exact ((Subgroup.mem_centralizer_iff.mp (hZα hz').2) x hx).symm
  have hc := centralizer_Zv_eq_Qv_of_bAt hA hα
  rw [inf_eq_left.mpr hcen] at hc
  exact pCoreOf_ne_stab hA α hc.symm

end F53.Stellmacher

end CFSG.Quasithin
