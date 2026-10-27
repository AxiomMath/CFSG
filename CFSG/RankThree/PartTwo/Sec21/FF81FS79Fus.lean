module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79TP
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Basic

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

structure Std (b t b₁ b₂ : H) (J : Subgroup H) where
  hyp : FS79Hyp b t b₁ b₂ J
  φ : ↥J ≃* J6.S6
  φ₁ : φ ⟨b₁, hyp.b₁_mem⟩ = J6.c₁
  φ₂ : φ ⟨b₂, hyp.b₂_mem⟩ = J6.c₂

noncomputable def FS79Hyp.std (h : FS79Hyp b t b₁ b₂ J) : Std b t b₁ b₂ J :=
  ⟨h, h.exists_std.choose, h.exists_std.choose_spec.1, h.exists_std.choose_spec.2⟩

noncomputable def Std.ι (S : Std b t b₁ b₂ J) : J6.S6 →* H :=
  J.subtype.comp S.φ.symm.toMonoidHom

theorem Std.ι_apply (S : Std b t b₁ b₂ J) (σ : J6.S6) : S.ι σ = (S.φ.symm σ : H) := rfl

theorem Std.ι_injective (S : Std b t b₁ b₂ J) : Function.Injective S.ι := by
  intro σ τ hστ
  exact S.φ.symm.injective (Subtype.ext hστ)

theorem Std.ι_mem (S : Std b t b₁ b₂ J) (σ : J6.S6) : S.ι σ ∈ J := (S.φ.symm σ).2

theorem Std.exists_ι (S : Std b t b₁ b₂ J) {j : H} (hj : j ∈ J) : ∃ σ, S.ι σ = j :=
  ⟨S.φ ⟨j, hj⟩, by simp [Std.ι_apply]⟩

theorem Std.ι_c₁ (S : Std b t b₁ b₂ J) : S.ι J6.c₁ = b₁ := by
  rw [Std.ι_apply, ← S.φ₁]
  simp

theorem Std.ι_c₂ (S : Std b t b₁ b₂ J) : S.ι J6.c₂ = b₂ := by
  rw [Std.ι_apply, ← S.φ₂]
  simp


theorem FS79Hyp.zpowers_inf_J (h : FS79Hyp b t b₁ b₂ J) : Subgroup.zpowers b ⊓ J = ⊥ := by
  have hcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord_b]
  have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ J) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers b ⊓ J ≤ Subgroup.zpowers b)
    rwa [hcard] at this
  apply Subgroup.eq_bot_of_card_eq
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact h1
  · exfalso
    have heq : Subgroup.zpowers b ⊓ J = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
    have hbJ : b ∈ J := by
      have : b ∈ Subgroup.zpowers b ⊓ J := by rw [heq]; exact Subgroup.mem_zpowers b
      exact this.2
    exact h.b_not_mem_J hbJ

theorem FS79Hyp.B_inf_J (h : FS79Hyp b t b₁ b₂ J) {w : H}
    (hw : w ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) (hwJ : w ∈ J) :
    w ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
  have hw' : w ∈ Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂} : Set H) := by
    rwa [closure_bb₁b₂_eq] at hw
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ c ∈ Subgroup.closure ({b₁, b₂} : Set H),
      Commute a c := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
      (h.J_le_cen_b (h.B₁_le_J hc)) : Commute c b) k).symm
  obtain ⟨u, hu, z, hz, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hw'
  have huJ : u ∈ J := by
    have := J.mul_mem hwJ (J.inv_mem (h.B₁_le_J hz))
    simpa using this
  have : u ∈ Subgroup.zpowers b ⊓ J := ⟨hu, huJ⟩
  rw [h.zpowers_inf_J, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact hz

theorem FS79Hyp.isSylowOf_B_top (h : FS79Hyp b t b₁ b₂ J) :
    IsSylowOf 3 (Subgroup.closure ({b, b₁, b₂} : Set H)) ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  have hE := h.isElemAb_B
  rw [← hB] at hE
  haveI := hE.1
  have hB3 : IsPGroup 3 B := IsElementaryAbelian.isPGroup 3 B
  obtain ⟨P, hBP⟩ := hB3.exists_le_sylow
  have hPp : IsPGroup 3 (P : Subgroup H) := P.isPGroup'
  have hbB : b ∈ B := FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b)
  have hPC : (P : Subgroup H) ≤ Cen b := h.pgroup_le_cen hPp (hBP hbB)
  have hPN : (P : Subgroup H) ≤ Nor (Subgroup.zpowers b) := hPC.trans h.cen_le_nor
  obtain ⟨k, -, hk⟩ := L14.exists_conj_le_sylowOf (G := H) h.isSylow_B_N hPN hPp
  have hcard : Nat.card (P : Subgroup H) ≤ Nat.card B := by
    have h1 : Nat.card ((P : Subgroup H).map (MulAut.conj k).toMonoidHom) =
        Nat.card (P : Subgroup H) := Subgroup.card_map_of_injective (MulAut.conj k).injective
    rw [← h1]
    refine Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hPB : B = (P : Subgroup H) := Subgroup.eq_of_le_of_card_ge hBP hcard
  refine ⟨le_top, hB3, ?_⟩
  rw [Subgroup.relIndex_top_right, hPB]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr P.not_dvd_index

theorem FS79Hyp.mem_Nor_of_conj_b (h : FS79Hyp b t b₁ b₂ J) {g : H}
    (hg : g * b * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) :
    g ∈ Nor (Subgroup.zpowers b) := by
  have hbB : b ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b)
  have hcen : g * b * g⁻¹ ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.B_comm hg hbB)
  have hle : conjBy g (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : (MulAut.conj g).toMonoidHom (b ^ k) = (g * b * g⁻¹) ^ k := by
      simp [MulAut.conj_apply]
    rw [e]
    exact h.cen_le_nor (Subgroup.zpow_mem _ hcen k)
  have heq := h.weak g hle
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem FS79Hyp.fusion_B (h : FS79Hyp b t b₁ b₂ J) {x y g : H}
    (hx : x ∈ Subgroup.closure ({b, b₁, b₂} : Set H))
    (hy : y ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) (hg : g * x * g⁻¹ = y) :
    ∃ n ∈ Nor (Subgroup.closure ({b, b₁, b₂} : Set H)), n * x * n⁻¹ = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPs := h.isSylowOf_B_top
  have hcop' : ¬ 3 ∣ (Subgroup.closure ({b, b₁, b₂} : Set H)).index := by
    rw [← Subgroup.relIndex_top_right]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hPs.2.2
  obtain ⟨S, hS⟩ : ∃ S : Sylow 3 H, (S : Subgroup H) = Subgroup.closure ({b, b₁, b₂} : Set H) :=
    ⟨hPs.2.1.toSylow hcop', IsPGroup.toSylow_coe hPs.2.1 hcop'⟩
  haveI hcomm' : IsMulCommutative (S : Subgroup H) :=
    ⟨⟨fun a c => Subtype.ext (h.B_comm (by rw [← hS]; exact a.2) (by rw [← hS]; exact c.2))⟩⟩
  have hxS : x ∈ (S : Subgroup H) := by rw [hS]; exact hx
  have hyS : y ∈ (S : Subgroup H) := by rw [hS]; exact hy
  obtain ⟨n, hn, hn'⟩ := S.conj_eq_normalizer_conj_of_mem x g⁻¹ hxS
    (by rw [inv_inv, hg]; exact hyS)
  refine ⟨n⁻¹, ?_, ?_⟩
  · have hn2 : n ∈ Nor (S : Subgroup H) := hn
    have := (Nor (S : Subgroup H)).inv_mem hn2
    rwa [hS] at this
  · rw [inv_inv]
    rw [inv_inv, hg] at hn'
    exact hn'.symm


theorem FS79Hyp.nor_B_decomp (h : FS79Hyp b t b₁ b₂ J) {n : H}
    (hn : n ∈ Nor (Subgroup.closure ({b, b₁, b₂} : Set H))) :
    ∃ k ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ y ∈ Subgroup.closure ({b, t} : Set H),
      ∃ j ∈ J, n = k * (y * j) ∧
        (∀ z ∈ Subgroup.closure ({b₁, b₂} : Set H), n * z * n⁻¹ = j * z * j⁻¹) ∧
        ∀ z ∈ Subgroup.closure ({b₁, b₂} : Set H),
          j * z * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
  have hbB : b ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b)
  have hnb : n * b * n⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    (Subgroup.mem_normalizer_iff.mp hn b).mp hbB
  have hnN : n ∈ Nor (Subgroup.zpowers b) := h.mem_Nor_of_conj_b hnb
  obtain ⟨hrM, hk⟩ := h.rho_spec hnN
  obtain ⟨y, hy, j, hj, hyj⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set H)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hrM
  have hn_eq : n = (n * (h.rho n)⁻¹) * (y * j) := by
    rw [hyj]
    group
  have hconj : ∀ z ∈ Subgroup.closure ({b₁, b₂} : Set H), n * z * n⁻¹ = j * z * j⁻¹ := by
    intro z hz
    have hzJ := h.B₁_le_J hz
    have hwJ : j * z * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hzJ) (J.inv_mem hj)
    have hyw : y * (j * z * j⁻¹) = (j * z * j⁻¹) * y := h.Y_comm_J hy hwJ
    have hkw : (n * (h.rho n)⁻¹) * (j * z * j⁻¹) = (j * z * j⁻¹) * (n * (h.rho n)⁻¹) :=
      h.K_comm_J hk hwJ
    set k : H := n * (h.rho n)⁻¹ with hkdef
    calc n * z * n⁻¹ = k * (y * (j * z * j⁻¹) * y⁻¹) * k⁻¹ := by rw [hn_eq]; group
      _ = k * ((j * z * j⁻¹) * y * y⁻¹) * k⁻¹ := by rw [hyw]
      _ = k * (j * z * j⁻¹) * k⁻¹ := by group
      _ = (j * z * j⁻¹) * k * k⁻¹ := by rw [hkw]
      _ = j * z * j⁻¹ := by group
  refine ⟨n * (h.rho n)⁻¹, hk, y, hy, j, hj, hn_eq, hconj, ?_⟩
  intro z hz
  have hzJ := h.B₁_le_J hz
  have hzB := FS79Hyp.B₁_le_B b b₁ b₂ hz
  have hnz : n * z * n⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    (Subgroup.mem_normalizer_iff.mp hn z).mp hzB
  have hwJ : j * z * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hzJ) (J.inv_mem hj)
  have hnzJ : n * z * n⁻¹ ∈ J := by rw [hconj z hz]; exact hwJ
  rw [← hconj z hz]
  exact h.B_inf_J hnz hnzJ

theorem FS79Hyp.nor_B_mono (h : FS79Hyp b t b₁ b₂ J) {n : H}
    (hn : n ∈ Nor (Subgroup.closure ({b, b₁, b₂} : Set H))) :
    n * b₁ * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H) ∧
      n * b₂ * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H) := by
  obtain ⟨k, hk, y, hy, j, hj, hn_eq, hconj, hjB⟩ := h.nor_B_decomp hn
  have hjnor : j ∈ J ⊓ Nor (Subgroup.closure ({b₁, b₂} : Set H)) :=
    ⟨hj, Subgroup.mem_normalizer_fintype hjB⟩
  have hb₁ : b₁ ∈ Subgroup.closure ({b₁, b₂} : Set H) := Subgroup.subset_closure (by simp)
  have hb₂ : b₂ ∈ Subgroup.closure ({b₁, b₂} : Set H) := Subgroup.subset_closure (by simp)
  rw [hconj b₁ hb₁, hconj b₂ hb₂]
  exact ⟨h.mono j hjnor b₁ (by simp), h.mono j hjnor b₂ (by simp)⟩

theorem FS79Hyp.fusion_b₁ (h : FS79Hyp b t b₁ b₂ J) {g : H}
    (hg : g * b₁ * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) :
    g * b₁ * g⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H) := by
  have hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ (Subgroup.subset_closure (by simp))
  obtain ⟨n, hn, hnb⟩ := h.fusion_B hb₁B hg rfl
  rw [← hnb]
  exact (h.nor_B_mono hn).1

theorem FS79Hyp.fusion_b₂ (h : FS79Hyp b t b₁ b₂ J) {g : H}
    (hg : g * b₂ * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) :
    g * b₂ * g⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H) := by
  have hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.B₁_le_B b b₁ b₂ (Subgroup.subset_closure (by simp))
  obtain ⟨n, hn, hnb⟩ := h.fusion_B hb₂B hg rfl
  rw [← hnb]
  exact (h.nor_B_mono hn).2

end CFSG.RankThree.PartTwo.Sec21.FF81
